object Lab2Main {
  import jsy.lab2._
  import Lab2_pekl2737.evaluate // change this to reference your lab object
  
  var debug = false /* set to false to disable debugging output */
  
  val opts = new options.Options(List(
    ("debug", options.SetBool(b => debug = b, Some(b => debug == b)), "debugging")
  ))
  
  def main(args: Array[String]) {
    val file: String = 
      opts.process(args) match {
        case file :: Nil => file
        case _ => opts.usageErr()
      }
    
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = evaluate(expr)
    
    println("\nValue:\n  " + v)
  }

}

object options {
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
        
       input     A file containing a JavaScripty program.
        
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