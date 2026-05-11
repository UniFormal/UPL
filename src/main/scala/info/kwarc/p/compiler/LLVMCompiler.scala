package info.kwarc.p.compiler

import info.kwarc.p.Program

import java.io.OutputStreamWriter
import java.nio.charset.StandardCharsets

object LLVMCompiler {
  def run(p: Program) = {
    val cp = new LLVMCompiler()

    val pb = new ProcessBuilder(
      "clang",
      "-x", "ir",
      "-",
      "-o", "out"
    )
    pb.redirectErrorStream(true)
    val process = pb.start

    val writer = new OutputStreamWriter(process.getOutputStream, StandardCharsets.UTF_8)
    try {
      writer.write(cp.compile(p))
    } finally writer.close()
    process.waitFor()
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