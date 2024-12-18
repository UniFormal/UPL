package info.kwarc.p

import java.io._
import scala.collection._

/** like File, but used to avoid any dependency on java.io.File */
case class SourceOrigin(path: String) {
  override def toString = path
}

case class File(toJava: java.io.File) {
   def /(s: String) = File(new java.io.File(toJava, s))
   def canonical : File = File(toJava.getCanonicalPath)
   override def toString = toJava.toString
   def toSourceOrigin = SourceOrigin(toString)
}

/** copied from mmt-api */
object File {
  /** constructs a File from a string, using the java.io.File parser */
  def apply(s: String): File = File(new java.io.File(s))

  /**
   * convenience method for reading a file into a string
   *
   * @param f the source file
   * @return s the file content (line terminators are \n)
   */
  def read(f: File): String = {
    val s = new StringBuilder
    ReadLineWise(f) {l => s.append(l + "\n")}
    s.result()
  }

  /** convenience method to obtain a typical (buffered, UTF-8) reader for a file */
  def Reader(f: File): BufferedReader = new BufferedReader(new InputStreamReader(new FileInputStream(f.toJava),
    java.nio.charset.Charset.forName("UTF-8")))

  /** convenience method to read a file line by line
    * @param f the file
    * @param proc a function applied to every line (without line terminator)
    */
  def ReadLineWise(f: File)(proc: String => Unit) = {
    val r = Reader(f)
    var line: Option[String] = None
    try {
      while ( {
        line = Option(r.readLine)
        line.isDefined
      })
        proc(line.get)
    } finally {
      r.close
    }
  }
}
