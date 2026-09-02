package info.kwarc.p

import info.kwarc.p.File.readAsSource

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
    implicit def gc: GlobalContext = GlobalContext(bg).enter(currentStage.module.df)

    @inline def asModule: Module = currentStage.module.copy(name = "LoWo")
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

    /** Lookup a fact in the [[LoWo]]
      * @param name The name of the fact
      * @param f A [[PartialFunction]] used to extract the fact from the interpreted definiens.
      *                  Can be an extractor in the scala sense, but doesn't need to.
      * @see [[lookup]]
      */
    @inline
    def lookupWithPF[T<:Object,A](name: String, f: PartialFunction[T,A]): Option[A] =
      lookup(name,f.lift)

    /** Lookup a [[ValueFact]]
      * @see [[lookup]]
      */
    @inline
    def lookupValueFact(name:String): Option[(Ref, List[Expression], Double)] =
      lookup(name+"_P", ValueFact.unapply _)

    /** Lookup a Number
      * @see [[lookup]]
      */
    @inline
    def lookupNum(name:String): Option[Double] =
      lookup(name, RealValue.unapply).map(_.approx.value)

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

    @inline
    def add(decls_String: String): Boolean = add(Seq(decls_String))
    def add(decls_String: Seq[String]): Boolean = {
      val prev = currentStage.label
      step()
      val curr = currentStage.label
      val stageString =
        s"theory $curr{\ninclude $prev \n${decls_String.mkString("\n")}\n}"
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

  /** Intermediate Stages of the Situation */
  case class Stage(num: Int) extends ProjectEntry(SourceOrigin("Stage", num.toString)) {
    val label: String = source.container ++ source.fragment

    /** Checked context */
    def cxt =  GlobalContext(checked)

    def module: Module = cxt.lookupModule(OpenRef(Path(label)))

    def asInstance: Instance = {
      Instance(Theory(
        module.decls.mapConserve {
          case d: ExprDecl if d.dfO.isEmpty => d.copy(dfO = Option(UndefinedValue(d.tp)))
          case d => d
        }
      ))
    }
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
  case class Schema(name: String, dataNeededToGenerateSchemaApplication: Nothing) extends ProjectEntry(SourceOrigin(name)) {
    //def apply(stage: Stage, data: Nothing): Stage = ???
    def df: Module = checked.decls.collectFirst{case Module(`name`,_,_) => df}.get
  }
  object Schema {
    /** constant entry for applications */
    val appEntry: ProjectEntry = get(SourceOrigin("Stage","SchemaApplication"))
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
    val appLabel = "Application"
//    var reqDecls = requiredFactsAssignment map {case (n, d) => s"$n = .${currentStage.label}.$d"} mkString "\n"
//    reqDecls += requiredFactsAssignment collect {case (n, d) if currentStage.pDecls.declares(s"${n}_P") => s"${n}_P = ${d}_P"} mkString "\n"
//    val apCode = s"theory $appLabel{\n$reqDecls\nrealize $schema}"
    var reqDecls = requiredFactsAssignment map {case (n, d) => s"$n = $d"} mkString "\n"
    reqDecls += requiredFactsAssignment collect {case (n, d) if currentStage.cxt.declares(s"${n}_P") => s"${n}_P = ${d}_P"} mkString "\n"
    val apCode = s"theory $appLabel{\ninclude ${currentStage.label}\n$reqDecls\nrealize $schema}"
    val apRaw = updateAndCheck(Schema.appEntry, apCode).lookup(appLabel).asInstanceOf[Module]
    if (Schema.appEntry.errors.hasErrors) {
      return false
    }
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
    val solved = subbed.copyBody(
      _.filterNot(d => d.nameO.exists(assignedNames.contains) || d.isInstanceOf[Include])
      ++: resDecls
    )
    LoWo.add(resDecls.map(_.toString))
  }

  @inline
  private def findSchema(name: String): Option[Module] = {
    entries.collectFirst({e:ProjectEntry => e.checked.lookupO(name).asInstanceOf[Module]})
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
