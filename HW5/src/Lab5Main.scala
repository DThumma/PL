import java.io.File
object Lab5Main {
  import jsy.util._
  import jsy.lab5._
  import Lab5_pekl2737.{removeInterfaceDecl,inferType, step} // change this to reference your lab object
  
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
      ast.checkClosed(expr)
    }} match {
      case None => return
      case r => r
    }
    
    if (debug) { println("Removing interface declarations ...") }
    
    val Some(expr1) =
      handle(None: Option[ast.Expr]) {Some{
        removeInterfaceDecl(expr)
      }} match {
        case None => return
        case r => r
      }
      
    if (debug) {
      println("  %s".format(expr1))
      println("------------------------------------------------------------")
      println("Type checking ...")
    }
    
    val Some(ty) =
      handle(None: Option[ast.Typ]) {Some{
        inferType(expr1)
      }} match {
        case None => return
        case r => r
      }
    
    if (debug) {
      println(ast.pretty(ty))
      println("------------------------------------------------------------")
      println("Evaluating with Small-Step Interpreter ...")
    }
    
    def evaluateWithStep(m: Map[ast.A, ast.Expr], e: ast.Expr, n: Int): (Map[ast.A, ast.Expr], ast.Expr) = {
      if (debug && debugSteps) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
      if (ast.isValue(e)) (m, e)
      else {
        val (mp, ep) = step(m, e)
        evaluateWithStep(mp, ep, n + 1)
      }
    }
    
    handle() {
      val (_, v1) = evaluateWithStep(Map.empty, expr1, 0)
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
