package info.kwarc.p

import info.kwarc.p.File.readAsSource

import scala.collection.mutable
import scala.util.Try

/**
  * A FrameIT SituationTheory (SiTh) is semantically a mutable UPL theory (i.e. a closed [[Module]]),
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

/**
  * A FrameIT Project has a "SituationTheory" (SiTh), a UPL theory (i.e. a closed [[Module]]) which can grow over time.
  * This is implemented via a special [[ProjectEntry]]
  * Its current value is accessible as [[SiTh]], and new declarations can be added via [[Stage.add]]
  */
class FrameITProject private extends Project(Nil,None){
  final val debug: Boolean = false

  /** The current logical world
    *
    * This is essentially a constant handle for the latest [[Stage]], with interface sugar
    */
  object SiTh{
    private val proj = FrameITProject.this

    /** Set the [[SiTh]] to the combination of all [[Declaration Declarations]] of all [[Stage Stages]] */
    //def update(): TheoryValue = update(s"theory SiTh{include ${Stage.current}}")

    /** @throws NoSuchElementException if SiTh cannot be found or is not a theory.
      *
      * Which should not be possible
      */
    def get: Module = {
      val voc = proj.check(Stage.Origin.current,false)
      voc.lookup(Stage.name_curr) match {
        case m:Module => m
        case _ => throw new NoSuchElementException("SiTh is not a Theory")
      }
    }

    def lookup(name:String): Declaration = {
      get.lookup(name)
    }

    def decls: List[Declaration] = get.decls
    override def toString: String =
      s"{\n ${decls.mkString("\n").indent(1)} \n}"

    def errors: ErrorCollector = Stage.current.errors
  }

  /** Intermediate Stages of the Situation
    *
    * There might be a point in having the Stages encapsulated in their own "Project", the Frame
    */
  case class Stage(num: Int = Stage.counter) extends ProjectEntry(Stage.Origin(num))
  object Stage {
    var counter = 0
    def current: Stage = get(Origin(counter)).asInstanceOf[Stage]
    def name_curr: String = makeName(counter)
    def name_prev: String = makeName(counter - 1)
    private def makeName(num: Int) = s"Stage$num"
    /** Extractor, because [[SourceOrigin]] is a case class and cannot be extended */
    object Origin {
      def current: SourceOrigin = apply(counter)
      def apply(num: Int): SourceOrigin = SourceOrigin(makeName(num))

      def unapply(so: SourceOrigin): Option[Int] = so match {
        case SourceOrigin(s"Stage$num", null) => num.toIntOption
        case _ => None
      }
    }

    def add(decls_String: String): Boolean = {
      counter += 1
      val stageString = s"theory $name_curr{\ninclude $name_prev\n$decls_String\n}"
      val checked = updateAndCheck(Origin(counter), stageString)
      // Remove the 'Include's
      val filtered = checked.decls.collect{
        case m:Module => m.copyF(_.filterNot(_.isInstanceOf[Include]))
      }
      get(Origin(counter)).checked = checked.copy(filtered)
      val err = hasErrors
      if (err) undo()
      !err
    }

    def add(decls: Iterable[Declaration]): Boolean = add(decls.mkString("\n"))

    def undo(): Unit = {
      entries = entries.init
      counter -= 1
    }
  }

  /** Unlike the content of `BackgroundTheory`, Schemata (formerly Scrolls) operate on the Frame itself,
    * and should thus be first-class citizen of the Project.
    *
    * @todo Actually implement this; The application of a Schema is completely manual rn.
    *       Also add a dedicated SourceOrigin/Extractor then.
    */
  case class Schema(name: String, dataNeededToGenerateSchemaApplication: Nothing) extends ProjectEntry(SourceOrigin(name)) {
    //def apply(stage: Stage, data: Nothing): Stage = ???
  }

  /** Apply [[Schema]] to deduce the resulting Facts from the required ones.
    *
    * @param schema the name of the schema to apply
    * @param requiredFactsAssignment
    * @param resultingFactsAssignment
    * @return `true` if the Schema application was successful
    * @note We use [[collection.Map]] because
    *       - the order of requiredFactsAssignment doesn't matter if we `realize $schema` only afterwards, and
    *       - [[scalajs.js.Dictionary]] is implicitly convertible to [[mutable.Map]].
    *       - the mutability is not used
    */
  def applySchema(schema: String,
                  requiredFactsAssignment: collection.Map[String, String],
                  resultingFactsAssignment: collection.Map[String, String])
  : Boolean = {
    val (apOrigin,apName) = (SourceOrigin.anonymous,"Application")
    val reqDecls = requiredFactsAssignment map {case (n, d) => s"$n = $d"} mkString "\n"
    val apCode = s"theory $apName{\ninclude ${Stage.name_curr}\n$reqDecls\nrealize $schema}"
    val apRaw = updateAndCheck(apOrigin, apCode).lookup(apName).asInstanceOf[Module]
    //val apRaw = Solver.solve(makeGlobalContext(),OpenRef(Path(s"$apName")))
    val gc = GlobalContext(apRaw)
    val sub: Substitution = Substitution(
      (requiredFactsAssignment.toList ::: resultingFactsAssignment.toList)
        map {case (n, d) => EVarDecl.sub(n,ClosedRef(d))}
    )

    val subbed = Regional_Substituter(gc, sub, apRaw)
    // take only the actual results
    val resDecls = subbed.decls.collect { case d: ExprDecl
      if resultingFactsAssignment.contains(d.name) => d.copy(name= resultingFactsAssignment(d.name))
    }
    // "proper" solving with editing the theory; No point in that rn
    val assignedNames = requiredFactsAssignment.keySet ++ resultingFactsAssignment.keySet
    val solved = subbed.copyF(
      _.filterNot(d => d.nameO.exists(assignedNames.contains) || d.isInstanceOf[Include])
      ++: resDecls
    )
    Stage.add(resDecls)
  }

  @inline
  private def findSchema(name: String): Option[Module] = {
    entries.collectFirst({e:ProjectEntry => e.checked.lookupO(name).asInstanceOf[Module]})
  }

  def reset(): Unit = {
    Stage.counter = 0
    entries = entries.filterNot(e => e.isInstanceOf[Stage])
  }

  /** Find the corresponding [[ProjectEntry]] in [[entries]].
    *
    * If there isn't one yet: Create it, and insert at the end
    */
  override def get(so: SourceOrigin): ProjectEntry = entries.find(_.source == so).getOrElse {
    val e = so match {
      case Stage.Origin(n) => Stage(n)
      case _ => new ProjectEntry(so)
    }
    entries = entries :+ e
//    entries = entries match {
//      case es :+ sith => es :+ e :+ sith
//      case _ => List(e)
//    }
    e
  }
  def tryEval(input: String) = {
    Try{
      val parsed = Parser.expression(SourceOrigin.anonymous, input, ErrorThrower)
      val gc = makeGlobalContext()
      val (checked, _) = ThrowingChecker.checkAndInferExpression(gc, parsed)
      val (_, r) = Interpreter.run(Program(gc.voc.df, checked))
      r
    }
  }

  def checkAll()= {
    val (dirty,checked) = entries.view.filter(_.global).partition(_.checkedIsDirty)
    val voc: mutable.Queue[Declaration] = mutable.Queue.from(checked.flatMap(_.checked.decls))
    dirty.foreach{ le =>
      if(!le.errors.hasErrors) {
        val ch = new Checker(le.errors)
        le.checked = ch.checkVocabulary(GlobalContext(TheoryValue(voc.toList)), le.parsed, true)(le.parsed)
        le.checkedIsDirty = false
      }
      voc ++= le.getVocabulary.decls
    }
    TheoryValue(voc.toList)
  }

  def debugPrintVerbose(): Unit = println (entries.map(_.getVocabulary).mkString("\n"))
}

object FrameITProject {
  /**
    * Create a FrameIT project from an unfolded UPL project-file
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
  def apply(fileContents: Map[String, LazyList[(SourceOrigin, String)]]): FrameITProject = {
    val saveFileContents =  fileContents.withDefaultValue(LazyList.empty)
    val sourceKinds = List("background", "source", "schemata").view // List because we need the order for `entries`
    val entries = for {
      k <- sourceKinds
      (source, content) <- saveFileContents(k)
    } yield ProjectEntry(source, content)
    val project = new FrameITProject()
    project.entries = entries ++: project.entries // prepend the background, SiTh remains last element
    val siO = for {
      l <- fileContents get "stageInit"
      (_ , c) <- l.headOption
    } yield c
    val stageInitCode = s"theory ${project.Stage.name_curr}{${siO.getOrElse("")}}"
    project.update(SourceOrigin("InitialStage"), stageInitCode)
    project.checkAll()
    project
  }

  /** Convenience method for providing a single background, ect. in code  */
  def apply(backgroundContent: String, schemataContent:String, initialStageContent:String=""): FrameITProject = {
    val contents: Map[String, LazyList[(SourceOrigin, String)]] = Map(
      ("background", LazyList((SourceOrigin("Background"), backgroundContent))),
      ("schemata",   LazyList((SourceOrigin("Background"), schemataContent))),
      ("stageInit",  LazyList((SourceOrigin("InitialStage"), initialStageContent)))
    )
    FrameITProject(contents)
  }

  /**
    * Create a FrameIT project from a UPL project-file (*.pp)
    *
    * Relevant properties:
    *  - "background" (or "source") files are considered background and all content is added to the project as is
    *  - "schemata" ToDo Extract required and acquired facts from Schemata.
    *  - "stageInit" the first listed file is used as content for [[FrameITProject.Stage]]0. All others are ignored
    *
    * @param setupFile A UPL project-file (*.pp)
    * @return A fully set up FrameIt project
    */
  def apply(setupFile: File): FrameITProject = FrameITProject(unfoldProjectFile(setupFile.canonical))


  /** Kinda chimera of [[File.readPropertiesFromString]] and [[Project.fromFile]],
    * because both aren't quite flexible enough to be used here.  */
  private def unfoldProjectFile(projFile: File): Map[String, LazyList[(SourceOrigin, String)]] = {
    if (!(projFile.getExtension contains "pp")) {
      return Map(("background", LazyList.from(Project.pFiles(projFile).map(readAsSource))))
    }
    val r = scala.io.Source.fromFile(projFile.toJava)
    val props = new mutable.HashMap[String, LazyList[(SourceOrigin, String)]].withDefaultValue(LazyList.empty)
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
            .map{f => readAsSource(f)}
          props.updateWith(key) {
            case None => Option(value)
            case Some(old) => Option(old #::: value)
          }
        }
      }
    props.map{ case (k, v) => (k,v) }.toMap
  }
}
