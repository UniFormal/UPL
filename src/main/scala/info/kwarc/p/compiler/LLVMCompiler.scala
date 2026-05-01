package info.kwarc.p.compiler

import info.kwarc.p.Program

object LLVMCompiler {
  def run(p: Program) = {
    val cp = new LLVMCompiler()
    println(cp.compile(p))
    cp
  }
}

class LLVMCompiler {
  def compile(p: Program): String = {
    val ir = IRGenerator.run(p)

    val fnctDecls = ir.declaredFunctions.map(f => f.toLLVMDecl()).mkString("\n")
    val llvmStrcts = ir.structs.map(s => s.toLLVMStrct()).mkString("\n")
    val fncts = ir.functions.map(f => f.toLLVM()).mkString("\n")

    s"""
       |$fnctDecls
       |
       |$llvmStrcts
       |
       |$fncts
       |""".stripMargin
  }
}