package info.kwarc.p

import info.kwarc.p.File.readAsSource
import Util.LookupDecl

import scala.collection.mutable
import scala.util.Try

/**
  * A FrameIT Project has a logical world [[LoWo(LoWo)]], which can grow over time.
  * This is implemented via a series of theories, each including the previous one.
  */
class FrameITProject private extends Project(Nil,None){
  final val debug: Boolean = false
  private var _background: TheoryValue = Theory.empty
  def bg: TheoryValue = _background
  implicit def gc: GlobalContext = GlobalContext(currentStage.checked.add(bg.decls)).push(currentStage.ref)

  private var stageCounter = 0
  private var currentStage: Stage = Stage(0)

  /** The current logical world
    *
    * This is essentially an interface for the latest Stage (the [[Module]] and the [[ProjectEntry]]),
    * with a lot of additional sugar.
    *
    * Use the various [[lookup lookup*(name)]] methods to lookup facts, and [[add]] to add them.
    * [[asModule]] produces the entire LoWo
    */
  object LoWo {
    @inline def asModule: Module = currentStage.module.copy(name = "LoWo")
    def evalAll: Module = asModule.copyBody(_.map(evalDecl))
    @inline def decls: List[Declaration] = asModule.decls
    @inline override def toString: String = asModule.toString
    @inline def errors: ErrorCollector = currentStage.errors

    /** Lookup a fact in the [[LoWo]]
      * @param name The name of the fact
      * @param extractor The function used to extract the fact from the interpreted definiens.
      *                  Can be an extractor in the scala sense, but doesn't need to.
      * @return The value of the fact, interpreted and extracted.
      */
    def lookup[T<:Expression,A](name: String, extractor: T => Option[A] = Option.apply _): Option[A] = {
      Interpreter
        .quickRun(OwnedExpr(currentStage.asInstance,null,ClosedRef(name)))
        .collect{ case t: T => t }
        .flatMap(extractor)
    }
    def lookupFact[F<:Fact](name: String, factClass: FactClass[F]): Option[F] = {
      for {
        decl:ExprDecl <- currentStage.module.lookupDecl[ExprDecl](name).map(evalEDecl)
        axO:Option[ExprDecl] = currentStage.module.lookupDecl[ExprDecl](name+"_P").map(evalEDecl)
        fact <- factClass.fromDecls.unapply((decl, axO))
      } yield fact
    }

    /** Lookup a fact in the [[LoWo]]
      * @param name The name of the fact
      * @param f A [[PartialFunction]] used to extract the fact from the interpreted definiens.
      *                  Can be an extractor in the scala sense, but doesn't need to.
      * @see [[lookup]]
      */
    @inline
    def lookupWithPF[T<:Object,A](name: String, f: PartialFunction[T,A]): Option[A] =
      lookup(name,f.lift)

    /** Lookup a [[ValueFactHelper]]
      *
      * @see [[lookup]]
      */
    @inline
    def lookupValueFact(name:String): Option[(Ref, List[Expression], Double)] =
      lookup(name+"_P", ValueFactHelper.evalFromDefAx)

    /** Lookup a Number
      * @see [[lookup]]
      */
    @inline
    def lookupNum(name:String): Option[Double] =
      lookup(name, ValueFactHelper.tryConvertToDouble)

    @inline
    def eval(name:String): Option[Expression] = evalTyped(name).map(_._1)
    def evalTyped(name: String): Option[(Expression, Type)] = {
      Try{
        val parsed = OwnedExpr(currentStage.asInstance,null,ClosedRef(name))
        val (checked, tp) = ThrowingChecker.checkAndInferExpression(gc,parsed)
        val (_, r) = Interpreter.run(Program(bg,checked))
        (r,tp)
      }.toOption
    }

    private def evalDecl(decl: Declaration): Declaration = {
      decl match {
        case ed: ExprDecl => evalEDecl(ed)
        case _ => decl
      }
    }

    private def evalEDecl(ed: ExprDecl): ExprDecl =
      ed.copy(dfO = Interpreter.quickRun(OwnedExpr(currentStage.asInstance, null, ClosedRef(ed.name))))

    @inline
    def add[T](decls: Seq[T]): Boolean = add(decls.mkString("\n"))
    def add(decls_String: String): Boolean = {
      val prev = currentStage.label
      step()
      val curr = currentStage.label
      val stageString =
        s"""theory $curr{
           |include $prev
           |$decls_String
           |}""".stripMargin
      val checked = updateAndCheck(currentStage, stageString)
      // Remove the Include; It is always the first Declaration, because that's how stageString is built
      val filtered = checked.decls.collect{ case m:Module => m.copyBody(_.drop(1)) }
      currentStage.checked = checked.copy(decls = filtered)
      val err = currentStage.errors.hasErrors
      if (err) unstep()
      !err
    }

    private def step(): Unit ={
      stageCounter += 1
      currentStage = get(Stage.origin()).asInstanceOf[Stage]
    }
    def unstep(): Unit ={
      stageCounter -= 1
      currentStage.clear()
      currentStage = get(Stage.origin()).asInstanceOf[Stage]
    }

    /** Reset the state of the LoWo
      */
    def reset(): Unit = {
      entries = entries.filterNot(_.isInstanceOf[Stage])
      stageCounter = 0
      currentStage = Stage.initial
      entries :+= currentStage
    }
  }

  trait singleModule extends ProjectEntry {
    val label: String = source.container ++ source.fragment

    /** Checked context */
    def cxt =  GlobalContext(checked)

    val ref: OpenRef = OpenRef(Path(label))
    lazy val module: Module = cxt.lookupModule(ref)
    lazy val asInstance: Instance = {
      val addUndefs = module.decls
        .collect { case d: ExprDecl if d.dfO.isEmpty => d.copy(dfO = Option(UndefinedValue(d.tp)))}
      Instance(Theory(Include(ref) +: addUndefs))
    }

  }

  /** Intermediate Stages of the Situation */
  case class Stage(num: Int) extends ProjectEntry(SourceOrigin("Stage", num.toString)) with singleModule {
  }
  object Stage {
    val initial = Stage(0)
    def origin(num: Int=stageCounter): SourceOrigin = SourceOrigin("Stage", num.toString)

    /** Extractor for the [[SourceOrigin]] of a [[Stage]],
      * because [[SourceOrigin]] is a case class and cannot be extended */
    def unapply(so: SourceOrigin): Option[Int] = so match {
      case SourceOrigin("Stage", num) => num.toIntOption
      case _ => None
    }
  }

  /** Unlike the content of `BackgroundTheory`, Schemata (formerly Scrolls) operate on the Frame itself,
    * and should thus be first-class citizen of the Project.
    *
    * @todo Actually implement this; The application of a Schema is completely manual rn.
    *       Also add a dedicated SourceOrigin/Extractor then.
    */
  case class Schema(name: String, dataNeededToGenerateSchemaApplication: Any)
    extends ProjectEntry(SourceOrigin(name)) with singleModule {
      lazy val slots: List[Fact] = {
        val cleanedModule = module.copyBody(_.filterNot(_.defined))
        FactUtil.listFacts(cleanedModule)
      }
  }
  object Schema {
    /** constant entry for applications */
    val appEntry: ProjectEntry = get(SourceOrigin("Stage","SchemaApplication"))
  }

  /** Apply [[schemaName]] to deduce the resulting facts from the required ones.
    *
    * @param schemaName the name of the schema to apply
    * @param requiredFactsAssignment assignment of the required facts. Key and value are treated as an unpacked [[ClosedRef]]
    * @param resultingFactsAssignment
    * @return `true` if the Schema application was successful
    * @note We use [[collection.Map]] because
    *       - the order of requiredFactsAssignment doesn't matter if we `realize $schema` only afterwards, and
    *       - [[scalajs.js.Dictionary]] is implicitly convertible to [[mutable.Map]].
    *       - the mutability is not used
    */
  def applySchema(schemaName: String,
                  requiredFactsAssignment: collection.Map[String, String],
                  resultingFactsAssignment: collection.Map[String, String])
  : Boolean = {
    val appLabel = "Application"
    val schema = findSchema(schemaName).getOrElse(return false)
    @inline
    def addDefiningAxioms(m:collection.Map[String, String]):collection.Map[String, String] =
      m ++ (m collect { case (n, d) if schema.declares(s"${n}_P") => (n+"_P",d+"_P") })
    val reqA = addDefiningAxioms(requiredFactsAssignment)
    val resA = addDefiningAxioms(resultingFactsAssignment)
    // val reqDecls = reqA map {case (n, d) => s"$n = $d"}
    val apCode =
      s"""theory $appLabel {
         |include ${currentStage.label}
         |${reqA map {case (n, d) => s"$n = $d"} mkString "\n"}
         |include $schemaName
         |}""".stripMargin
    val assignmentSub: Substitution = Substitution((reqA ++ resA).map {case (n, d) => EVarDecl.sub(n,ClosedRef(d))}.toList)
    val subber = new RenameRegional()(gc, assignmentSub)

    // prep done, now start Application
    val apRaw: Module = updateAndCheck(Schema.appEntry, apCode).lookupDecl(appLabel).getOrElse(return false)
    if (Schema.appEntry.errors.hasErrors) return false

    val resDecls = Solver(apRaw, false, debug)
      .decls.collect { case d: ExprDecl if resA.contains(d.name) => subber(d) }

    LoWo.add(resDecls)
  }

  @inline
  def findSchema(name: String): Option[Module] = {
    entries.view.map(_.checked).flatMap(_.lookupDecl[Module](name)).headOption
  }

  /** Find the corresponding [[ProjectEntry]] in [[entries]].
    *
    * If there isn't one yet: Create it, and insert at the end
    */
  override def get(so: SourceOrigin): ProjectEntry = entries.find(_.source == so).getOrElse {
    val e = so match {
      case Stage(n) => Stage(n)
      case _ => new ProjectEntry(so)
    }
    entries :+=  e
    e
  }
  def tryEval(input:String): Try[Expression] = tryEvalTyped(input).map(_._1)
  def tryEvalTyped(input: String): Try[(Expression, Type)] = {
    Try{
      val parsed = Parser.expression(SourceOrigin.anonymous, input, ErrorThrower)
      val gc = makeGlobalContext()
      val (checked, tp) = ThrowingChecker.checkAndInferExpression(gc, parsed)
      val (_, r) = Interpreter.run(Program(gc.voc.df, checked))
      (r,tp)
    }
  }

  /** Check all unchecked entries
    *
    * Has the same side effects as `entries.foreach(check(_,false))`, but is significantly more efficient.
    * @return The entire Project as one [[TheoryValue]]. Similar to [[check check(stopOnError)]],
    *         but the entry-order is more resistant to accidental forward-declarations, and
    *         only global entries are included
    */
  def checkAll(): TheoryValue = {
    val (d,c) = entries.view.partition(_.checkedIsDirty)
    val checked = c.filter(_.global)
    val (dirtyG,dirtyL) = d.partition(_.global)
    val voc: mutable.Queue[Declaration] = mutable.Queue.from(checked.flatMap(_.checked.decls))
    dirtyG.foreach{ le =>
      if(!le.errors.hasErrors) {
        val ch = new Checker(le.errors)
        le.checked = ch.checkVocabulary(GlobalContext(TheoryValue(voc.toList)), le.parsed, true)(le.parsed)
        le.checkedIsDirty = false
      }
      voc ++= le.getVocabulary.decls
    }
    dirtyL.foreach(le => check(le,false))
    TheoryValue(voc.toList)
  }

  def toStringVerbose: String = entries.flatMap(e => List
    (
      s"// ${e.source}",
      e.getVocabulary.decls.mkString("\n"))
    )
    .mkString("\n\n")
}

object FrameITProject {
  /**
    * Create a FrameIT project from an unfolded UPL project-file
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
  def apply(fileContents: Map[String, Seq[(SourceOrigin, String)]]): FrameITProject = {
    val saveFileContents =  fileContents.withDefaultValue(Seq.empty)

    // Add the Background knowledge
    val sourceKinds = List("background", "source", "schemata")
    val bgEntries = for {
      k <- sourceKinds
      (source, content) <- saveFileContents(k)
    } yield ProjectEntry(source, content)
    val project = new FrameITProject()
    project.entries = bgEntries.toList
    val bg = project.checkAll() // check all background entries in one go
    project._background = bg

    // Set up the initial Stage
    /** the initial Stage */
    val iS = project.Stage.initial
    // make it temporarily empty, so `include`s work
    project.updateAndCheck(iS, s"theory ${iS.label}{}")
    project.entries +:= iS // empty stage can safely be prepended
    // then add any initial content
    for {
      l <- fileContents get "stageInit"
      (_ , init) <- l
      _ <- init.headOption // Skip if empty
    } project.LoWo.add(init)
    if (project.currentStage != iS) {
      val initialStageContent = project.LoWo.asModule.copy(name=iS.label)
      project.updateAndCheck(iS, initialStageContent.toString)
      project.LoWo.reset()
    } // else: the initial Stage is indeed empty => nothing left to do
    project
  }

  /** Convenience method for providing a single background, ect. in code  */
  def apply(backgroundContent: String, schemataContent:String, initialStageContent:String=""): FrameITProject = {
    val contents: Map[String, Seq[(SourceOrigin, String)]] = Map(
      ("background", Seq((SourceOrigin("Background"), backgroundContent))),
      ("schemata",   Seq((SourceOrigin("Schemata"), schemataContent))),
      ("stageInit",  Seq((SourceOrigin("InitialStage"), initialStageContent)))
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
  private def unfoldProjectFile(projFile: File): Map[String, Seq[(SourceOrigin, String)]] = {
    if (!(projFile.getExtension contains "pp")) { // code file => interpret as background
      return Map(("background", Project.pFiles(projFile).map(readAsSource)))
    }
    val r = scala.io.Source.fromFile(projFile.toJava)
    val props = new mutable.HashMap[String, Seq[(SourceOrigin, String)]].withDefaultValue(Seq.empty)
    for {
      lineRaw <- r.getLines()
      line = lineRaw.strip()
      if !line.startsWith("//")
      splitIndex = line.indexOf(":")
      if splitIndex > 0
      (key, vals) = ((line take splitIndex).strip(), (line drop (splitIndex+1)).strip())
      if key.nonEmpty && vals.nonEmpty
      v <- vals.split("\\s").reverseIterator
      if v.nonEmpty
      f <- Project.pFiles(projFile.up.resolve(v))
      value = readAsSource(f)
    } props(key) +:= value
    props.toMap // make props immutable
  }
}
