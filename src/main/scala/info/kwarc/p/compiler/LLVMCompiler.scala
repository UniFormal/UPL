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
    val ir = IRGenerator.generate(p)

    val gen = new LLVMGenerator
    val llvmBody = gen.visitBlock(ir.main)

    s"""
define i32 @main() {
$llvmBody
}"""
  }
}