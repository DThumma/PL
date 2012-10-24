import java.io.File
object Lab4Main {
  import jsy.util._
  import jsy.lab4._
  import Lab4_pekl2737.{inferType, step} // change this to reference your lab object
  
  var debug = false /* set to false to disable debugging output */
  var debugSteps = true /* set to false to disable individual evaluation steps printing */
  var keepGoing = false /* set to true to keep going after exceptions */
  
  val anon = ("input",
    { case filename :: Nil => new File(filename) }: PartialFunction[List[String], File],
    "A file containing a JavaScripty program or a directory with .jsy files.")
    
  val opts = new options.Options("jsy", List(
    ("debug", options.SetBool(b => debug = b, Some(b => debug == b)), "debugging"),
    ("steps", options.SetBool(b => debugSteps = b, Some(b => debugSteps == b)), "debugging individual reduction steps"),
    ("keep-going", options.SetBool(b => keepGoing = b, Some(b => keepGoing == b)), "keep going after exceptions")
  ), anon)
  
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
      else {
        throw new IllegalArgumentException("File %s does not exist.".format(file))
      }
    }
    val file: File = opts.process(args)
    doFile(file)
  }
}
