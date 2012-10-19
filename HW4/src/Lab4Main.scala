import java.io.File
object Lab4Main {
  import jsy.lab4._
  
  import Lab4_pekl2737.{inferType, step} // change this to reference your lab object
  
  var debug = false /* set to false to disable debugging output */
  var debugSteps = true /* set to false to disable individual evaluation steps printing */
  var keepGoing = false /* set to true to keep going after exceptions */
  
  val opts = new lab4options.Options(List(
    ("debug", lab4options.SetBool(b => debug = b, Some(b => debug == b)), "debugging"),
    ("steps", lab4options.SetBool(b => debugSteps = b, Some(b => debugSteps == b)), "debugging individual reduction steps"),
    ("keep-going", lab4options.SetBool(b => keepGoing = b, Some(b => keepGoing == b)), "keep going after exceptions")
  ))
  
  def handle[T](default: T)(e: => T): T =
    if (!keepGoing) e
    else try e catch {
      case exn => println(exn.toString); default
    }
  
  def processFile(file: File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val Some(expr) =
      handle(None: Option[ast.Expr]) {Some{
        Parser.parseFile(file)
      }} match {
        case None => return
        case r => r
      }
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    handle(None: Option[Unit]) {Some{
      if (!ast.closed(expr))
        throw new IllegalArgumentException("Top-level expression must be closed for evaluation. Expression %s is not closed.".format(expr))
    }} match {
      case None => return
      case r => r
    }
    
    if (debug) { println("Type checking ...") }
    
    handle() {
      val t = inferType(expr)
      println(ast.pretty(t))
    }
    
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with Small-Step Interpreter ...")
    }
    
    def evaluateWithStep(e: ast.Expr, n: Int): ast.Expr = {
      if (debug && debugSteps) { println("Step %s: %s".format(n, e)) }
      if (ast.isValue(e)) e else evaluateWithStep(step(e), n + 1)
    }
    
    handle() {
      val v1 = evaluateWithStep(expr, 0)
      println(ast.pretty(v1))
    }
  }
  
  def isJsy(file: File): Boolean = {
    val jsyext = """[.]jsy$""".r
    jsyext findFirstIn file.getName match {
      case Some(_) => true
      case None => false
    }
  }
    
  def main(args: Array[String]) {
    def doFile(file: File) {
      if (file.isFile) {
        processFile(file)
      }
      else if (file.isDirectory) {
        file.listFiles filter isJsy foreach doFile
      }
    }
    val file: File = 
      opts.process(args) match {
        case filename :: Nil => new File(filename)
        case _ => opts.usageErr()
      }
    doFile(file)
  }
}

object lab4options {
  sealed abstract class Spec
  case class SetBool(setter: Boolean => Unit, default: Option[Boolean => Boolean]) extends Spec

  class Options(specs: List[(String, Spec, String)]) {
    import collection.mutable.HashMap
    
    val opts: Map[String, Unit => Unit] =
      (Map[String, Unit => Unit]() /: specs)((acc, spec) => spec match {
        case (name, SetBool(setter, _), _) =>
          acc +
          (("--" + name) -> ((_: Unit) => setter(true))) +
          (("--no-" + name) -> ((_: Unit) => setter(false)))
      })
      
    val descriptions: String = {
      def optline(name: String, text: String): String = {
        "%-8s".format("") + "%-15s".format(name) + "%s\n".format(text)
      }
      (specs :\ "")((spec, acc) => spec match {
        case (name, SetBool(_, default), desc) => {
          def defaultStr(b: Boolean): String =
            default map (f => if (f(b)) " (default)" else "") getOrElse("") 
          optline("--" + name, "turn on %s".format(desc) + defaultStr(true)) +
          optline("--no-" + name, "turn off %s".format(desc) + defaultStr(false)) +
          acc
        }
      })
    }
      
    def usageErr(): Nothing = {
      val header =
      """
Usage: jsy [options] input
        
       input     A file containing a JavaScripty program or a directory with .jsy files.
        
Options:
"""
      print(header + descriptions)
      exit(1)
    }
    
    def process(args: Array[String]): List[String] = {
      def loop(l: List[String]): List[String] = l match {
        case Nil => Nil
        case h :: t => opts.get(h) match {
          case None => l
          case Some(doit) => doit(); loop(t)
        }
      }
      loop(args.toList)
    }
  }
}