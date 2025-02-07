package info.kwarc.p

import java.io._
import scala.collection._

/** like File, but used to avoid any dependency on java.io.File
  * @param path an identifier of the document holding the sources, such as a file path or URL
  * @param frament if the document is split into multiple fragments (e.g., in a notebook consisting of cells), an identifier of the fragment
  */
case class SourceOrigin(path: String, fragment: String = null) {
  override def toString = path + (if (fragment != null) "#"+fragment else "")
}

case class File(toJava: java.io.File) {
   def /(s: String) = File(new java.io.File(toJava, s))
   def canonical : File = File(toJava.getCanonicalPath)
   override def toString = toJava.toString
   def toSourceOrigin = SourceOrigin(toString)

  /** name (including extension) */
  def getName = toJava.getName

  /** @return the last file extension (if any) */
  def getExtension: Option[String] = {
    val name = toJava.getName
    val posOfDot = name.lastIndexOf(".")
    if (posOfDot == -1) None else Some(name.substring(posOfDot + 1))
  }

  /** sets the file extension (replaces existing extension, if any) */
  def setExtension(ext: String): File = getExtension match {
    case None => File(toString + "." + ext)
    case Some(s) => File(toString.substring(0, toString.length - s.length) + ext)
  }

  /** appends a file extension (possibly resulting in multiple extensions) */
  def addExtension(ext: String): File = getExtension match {
    case None => setExtension(ext)
    case Some(e) => setExtension(e + "." + ext)
  }

  /** parent directory */
  def up: File = {
    val par = Option(toJava.getParentFile)
    if (par.isEmpty) this else File(par.get)
  }

  /** resolves an absolute or relative path string against this */
  def resolve(s: String): File = {
    val sf = new java.io.File(s)
    val newfile = if (sf.isAbsolute)
      sf
    else
      new java.io.File(toJava, s)
    File(newfile.getCanonicalPath)
  }

  /** @return children of this directory */
  def children: List[File] = {
    if (toJava.isFile) Nil else {
      val ls = toJava.list()
      if (ls == null) throw IError("directory does not exist or is not accessible: " + toString)
      ls.toList.sorted.map(this / _)
    }
  }
  /** @return subdirectories of this directory */
  def subdirs: List[File] = children.filter(_.toJava.isDirectory)

  /** @return all files in this directory or any subdirectory */
  def descendants: List[File] = children.flatMap {c =>
    if (c.toJava.isDirectory) c.descendants else List(c)
  }
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

  def readPropertiesFromString(s: String): mutable.Map[String, String] = {
    val properties = new scala.collection.mutable.ListMap[String, String]
    s.split("\n") foreach {line =>
      // usually continuation lines start with a space but we ignore those
      val tline = line.trim
      if (!tline.startsWith("//")) {
        val p = tline.indexOf(":")
        if (p > 0) {
          // make sure line contains colon and the key is non-empty
          val key = tline.substring(0, p).trim
          val value = tline.substring(p + 1).trim
          properties(key) = properties.get(key) match {
            case None => value
            case Some(old) => old + " " + value
          }
        }
      }
    }
    properties
  }
}
