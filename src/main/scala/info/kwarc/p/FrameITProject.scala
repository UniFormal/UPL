package info.kwarc.p

import info.kwarc.p.File.readAsSource

import scala.collection.mutable
import scala.util.Try

/** A FrameIT SituationTheory (SiTh) is semantically a mutable UPL theory (i.e. a closed [[Module]]),
  * used to store and deduce knowledge about the game-world. In practice, Modules are essentially an immutable
  * `List[Declaration]`, so a [[SiTh_handler]] provides the necessary functionality to pretend access to a
  * mutable [[Module]], while also ensuring nothing contradictory happens when mutating.
  *
  * This is more of an API specification, than an abstraction.
  */
//trait SiTh_handler {
//  def getSiTh: Module
//  def getSiThErrors: List[SError]
//  def add(decls_String: String): Boolean
//  def add(decls: List[Declaration]): Boolean = add(decls.mkString("\n"))
//  def reset(): Unit
//  def SiThDecls: List[Declaration]
//  //def remove(fact_name: String): Either[List[SError], Module]
//  //def eval: TheoryValue
//}

/** A FrameIT Project has a "SituationTheory" (SiTh), a UPL theory (i.e. a closed [[Module]]) which can grow over time.
  * This is implemented via a special [[ProjectEntry]]
  * Its current value is accessible as [[SiTh]], and new declarations can be added via [[Stage.add]]
  */
class FrameITProject private extends Project(Nil, None) {
  import info.kwarc.p.FrameITProject._
  final val debug: Boolean = false
  entries = Vector(SiTh)
  main = Option(Parser.expression(SiThOrigin, "SiTh{}", ErrorIgnorer))

  /** The current Situation is always the latest Stage, but with a constant Name ("SiTh") */
  case object SiTh extends ProjectEntry(SiThOrigin) {
    private val proj = FrameITProject.this
    def context: GlobalContext =GlobalContext(get)

    /** Set the SiTh to the combination of all [[Declaration]]s of all SiThFragments */
    def update(): TheoryValue = update(s"theory SiTh{include ${Stage.current}}")

    /** @throws NoSuchElementException if no SiTh can be found or created.
      * @throws ClassCastException if SiTh is not a theory
      *
      * Neither should be possible
      */
    def get: Module = {
      update()
      proj.check(SiThOrigin, false)
      getVocabulary.lookupT[Module]("SiTh")
    }

    def decls: List[Declaration] = get.decls
    override def toString: String = {
      s"""${source} ::
         |${decls.mkString("{\n", "\n", "\n}").indent(1)}
         |${errors}""".stripMargin
    }
  }

  /** Intermediate Stages of the Situation
    *
    * There might be a point in having the Stages encapsulated in their own "Project", the Frame
    */
  case class Stage(num: Int = Stage.counter)
      extends ProjectEntry(Stage.Origin(num)) {

    /** Technically redundant, because `toString` results in the same */
    val name = source.container
  }
  object Stage {
    var counter = 0
    def current: Stage = get(Origin(counter)).asInstanceOf[Stage]
    def previous: Stage = get(Origin(counter - 1)).asInstanceOf[Stage]
    private def makeName(num: Int) = s"Stage$num"

    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def apply(num: Int = Stage.counter): SourceOrigin = SourceOrigin(
        makeName(num)
      )

      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin(s"Stage$num", null) => num.toIntOption
        case _                                => None
      }
    }

//    def apply(decls: Iterable[Declaration]): Boolean = {
//      if (decls.isEmpty) return false
//      counter += 1
//      val e = get(Origin())
//      e.parsed = TheoryValue(decls).withLocationFromTo(decls.head, decls.last)
//      DependencyAnalyzer.update(e)
//      e.checkedIsDirty = true
//      check(Origin(), false)
//      finalizeUpdate()
//    }

    def add(decls_String: String): Boolean = {
      counter += 1
      val stageString = s"theory $current{include $previous $decls_String}"
      updateAndCheck(Origin(counter), stageString)
      finalizeUpdate()
    }

    def add(decls: Iterable[Declaration]): Boolean = add(decls.mkString(" "))

    private def finalizeUpdate(): Boolean = {
      SiTh.update()
      if (debug) println(check(SiThOrigin, false))
      val err = hasErrors
      if (err) undo()
      !err
    }

    def undo(): Unit = {
      entries match {
      case es :+ Stage(_) :+ sith =>
        entries = es :+ sith
        counter -= 1
        SiTh.update()
      case _          =>
    }
    }
  }

  /** Unlike the content of `BackgroundTheory`, Schemata (formerly Scrolls) operate on the Frame itself,
    * and should thus be first-class citizen of the Project.
    *
    * @todo Actually implement this; The application of a Schema is completely manual rn.
    *       Also add a dedicated SourceOrigin/Extractor then.
    */
  case class Schema(
      name: String,
      dataNeededToGenerateSchemaApplication: Nothing
  ) extends ProjectEntry(SourceOrigin(name)) {
    //def apply(stage: Stage, data: Nothing): Stage = ???
  }

  /** Helper Entry for the application of a Schema. For now, it's easiest to just keep them around. */
  case class SchemaApplication(num: Int)
      extends ProjectEntry(SchemaApplication.Origin(num))
  object SchemaApplication {
    var counter = 0
    def next: (SourceOrigin, String) = {
      counter += 1
      (Origin(counter), makeName(counter))
    }
    private def makeName(num: Int) = s"Application$num"

    /** Extractor, because SourceOrigin is a case class and cannot be extended */
    object Origin {
      def apply(id: Int = counter): SourceOrigin = SourceOrigin(makeName(id))

      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin(s"Application$num", null) => num.toIntOption
        case _                                      => None
      }
    }
  }

  /** Apply [[schema]] to deduce the [[resultingFacts]] from the [[requiredFacts]].
    *
    * @param schema the name of the schema to apply
    * @param requiredFactsAssignment
    * @param resultingFactsAssignment
    * @return `true` if the Schema application was successful
    * @note We use [[collection.Map]] because
    *       - [[scalajs.js.Map]] is implicitly convertible to [[mutable.Map]], but
    *       - mutability is not actually needed
    */
  def applySchema(
      schema: String,
      requiredFactsAssignment: collection.Map[String, String],
      resultingFactsAssignment: collection.Map[String, String]
  ): Boolean = {
    val (apOrigin, apName) = SchemaApplication.next
    val assignments = requiredFactsAssignment ++ resultingFactsAssignment
    val reqDecls = requiredFactsAssignment map { case (n, d) =>
      s"$n = $d"
    } mkString "\n"
    val apCode =
      s"theory $apName{include ${Stage.current} $reqDecls include $schema}"
    val apRaw = updateAndCheck(apOrigin, apCode).lookupT[Module](apName)
    //val apRaw = Solver.solve(makeGlobalContext(),OpenRef(Path(s"$apName")))
    implicit val gc = GlobalContext(apRaw)
    implicit val sub: Substitution = Substitution(
      assignments map { case (n, d) => EVarDecl.sub(n, ClosedRef(d)) }
    )

    val subber = new Substituter(gc)
    val tmp = apRaw.updatedDecls(
      _.collect {
        case e: ExprDecl if resultingFactsAssignment.contains(e.name) =>
          subber(e.copy(name = assignments(e.name)).copyFrom(e))
      }
    )
    Stage.add(tmp.decls)
//    val tmp2 = apRaw.updatedDecls(_.withFilter(_ match {
//      case Include(_,_,_) => false
//      case _ => true
//    }).map{
//      case e: ExprDecl if assignments.contains(e.name) =>
//        subber(e.copy(name = assignments(e.name)).copyFrom(e))
//      case d => d
//    })
//    val apSub = updateAndCheck(apOrigin, tmp2.toString).lookupT[Module](apName)
  }

  @inline
  private def findSchema(name: String): Option[Module] = {
    entries.collectFirst({ e: ProjectEntry =>
      e.checked.lookupOT[Module](name)
    }.unlift)
  }

  def reset(): Unit = {
    Stage.counter = 0
    entries = entries.filterNot(e =>
      e.isInstanceOf[Stage] || e.isInstanceOf[SchemaApplication]
    )
    SiTh.update()
  }
  def getSiThErrors: List[SError] = SiTh.errors.getErrors

  /** Find the corresponding [[ProjectEntry]] in [[entries]].
    *
    * If there isn't one yet, create it, and insert it as the __second to last__ entry, before the [[SiTh]]
    */
  override def get(so: SourceOrigin): ProjectEntry =
    entries.find(_.source == so).getOrElse {
      val e: ProjectEntry = so match {
        case Stage.Origin(n)             => Stage(n)
        case SchemaApplication.Origin(n) => SchemaApplication(n)
        case SiTh.source                 =>
          // Somehow, the SiTh got deleted => re-add it at the end
          entries = entries :+ SiTh
          return SiTh
        case _                           => new ProjectEntry(so)
      }
      entries = entries match {
        case es :+ SiTh => es :+ e :+ SiTh
        case _          => Vector(e)
      }
      e
    }

  def add(e: ProjectEntry) = {
    entries = entries.indexWhere(_.source == e.source) match {
      case -1 =>
        entries match {
          case es :+ sith => es :+ e :+ sith
          case _          => Vector(e)
        }
      case n => entries.updated(n, e)
    }
  }
  def tryEval(input: String) = {
    Try {
      val parsed =
        Parser.expression(SourceOrigin.anonymous, input, ErrorThrower)
      val voc = check(true)
      val (checked, tp) =
        ThrowingChecker.checkAndInferExpression(GlobalContext(voc), parsed)
      val (_, r) = Interpreter.run(Program(voc, checked))
      (r,tp)
    }
  }

  def checkAll() = {
    val (dirty, checked) =
      entries.view.filter(_.global).partition(_.checkedIsDirty)
    val voc: mutable.Queue[Declaration] =
      mutable.Queue.from(checked.flatMap(_.checked.decls))
    dirty.foreach { le =>
      if (!le.errors.hasErrors) {
        val ch = new Checker(le.errors)
        le.checked =
          ch.checkVocabulary(GlobalContext(voc), le.parsed, true)(le.parsed)
        le.checkedIsDirty = false
      }
      voc ++= le.getVocabulary.decls
    }
    TheoryValue(voc.toList)
  }

  def debugPrintVerbose(): Unit = println(
    entries.map(_.getVocabulary).mkString("\n")
  )
}

object FrameITProject {
  // SiTh: SituationTheory
  private val SiThOrigin: SourceOrigin = SourceOrigin("SiTh")

  /** Create a FrameIT project from an unfolded UPL project-file
    * Using LazyLists means we don't need to keep all file contents in Memory.
    *
    * This implementation avoids using files explicitly, so it can be exported via scala.js
    *
    * @param fileContents An unfolded UPL project-file (*.pp)
    *                     Relevant keys:
    *   - "background" (or "source") files are considered background and all content is added to the project as is
    *   - "schemata" ToDo Extract required and acquired facts from Schemata.
    *   - "stageInit" the first listed file is used as content for [[FrameITProject.Stage]]0. All others are ignored
    * @return A fully set up FrameIt project
    */
  def apply(
      fileContents: Map[String, LazyList[(SourceOrigin, String)]]
  ): FrameITProject = {
    val saveFileContents = fileContents.withDefaultValue(LazyList.empty)
    val sourceKinds =
      List(
        "background",
        "source",
        "schemata"
      ).view // List because we need the order for `entries`
    val entries = for {
      k <- sourceKinds
      (source, content) <- saveFileContents(k)
    } yield ProjectEntry(source, content)
    val project = new FrameITProject()
    project.entries =
      entries ++: project.entries // prepend the background, SiTh remains last element
    val siO = for {
      l <- fileContents get "stageInit"
      (_, c) <- l.headOption
    } yield c
    val stageInitCode = s"theory ${project.Stage.current}{${siO.getOrElse("")}}"
    project.update(SourceOrigin("InitialStage"), stageInitCode)
    project.checkAll()
    project
  }

  /** Convenience method for providing a single background, ect. in code */
  def apply(
      backgroundContent: String,
      schemataContent: String,
      initialStageContent: String = ""
  ): FrameITProject = {
    val contents: Map[String, LazyList[(SourceOrigin, String)]] = Map(
      ("background", LazyList((SourceOrigin("Background"), backgroundContent))),
      ("schemata", LazyList((SourceOrigin("Background"), schemataContent))),
      (
        "stageInit",
        LazyList((SourceOrigin("InitialStage"), initialStageContent))
      )
    )
    FrameITProject(contents)
  }

  /** Create a FrameIT project from a UPL project-file (*.pp)
    *
    * Relevant properties:
    *  - "background" (or "source") files are considered background and all content is added to the project as is
    *  - "schemata" ToDo Extract required and acquired facts from Schemata.
    *  - "stageInit" the first listed file is used as content for [[FrameITProject.Stage]]0. All others are ignored
    *
    * @param setupFile A UPL project-file (*.pp)
    * @return A fully set up FrameIt project
    */
  def apply(setupFile: File): FrameITProject = FrameITProject(
    unfoldProjectFile(setupFile)
  )

  /** Kinda chimera of [[File.readPropertiesFromString]] and [[Project.fromFile]],
    * because both aren't quite flexible enough to be used here.
    */
  private def unfoldProjectFile(
      projFile: File
  ): Map[String, LazyList[(SourceOrigin, String)]] = {
    if (!(projFile.getExtension contains "pp")) {
      return Map(
        (
          "background",
          LazyList.from(Project.pFiles(projFile).map(readAsSource))
        )
      )
    }
    val r = scala.io.Source.fromFile(projFile.toJava)
    val props = new mutable.HashMap[String, LazyList[(SourceOrigin, String)]]
      .withDefaultValue(LazyList.empty)
    r.getLines()
      .map(_.strip())
      .filter(!_.startsWith("//"))
      .foreach { line =>
        val p +: v = LazyList from line.split(":", 2)
        if (p.nonEmpty && v.nonEmpty) { // make sure line contains colon and the key is non-empty
          val key = p.strip()
          val value = v
            .flatMap(_.split("\\s"))
            .filter(_.nonEmpty)
            .flatMap(s => Project.pFiles(projFile.up.resolve(s)))
            .map { f => readAsSource(f) }
          props.updateWith(key) {
            case None      => Option(value)
            case Some(old) => Option(old #::: value)
          }
        }
      }
    props.map { case (k, v) => (k, v) }.toMap
  }
}
