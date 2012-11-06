package jsy.util

object options {
  sealed abstract class Spec
  case class SetBool(setter: Boolean => Unit, default: Option[Boolean => Boolean]) extends Spec

  class Options[T](program: String, specs: List[(String, Spec, String)], anon: (String, PartialFunction[List[String], T], String)) {
    val opts: Map[String, Unit => Unit] =
      (Map[String, Unit => Unit]() /: specs)((acc, spec) => spec match {
        case (name, SetBool(setter, _), _) =>
          acc +
          (("--" + name) -> ((_: Unit) => setter(true))) +
          (("--no-" + name) -> ((_: Unit) => setter(false)))
      })
      
    val (anonName, anonDo, anonDesc) = anon
      
    val nameWidth: Int = opts.foldLeft(anonName.length){ case (acc, (n, _)) => acc max n.length }
    
    def padRight(s: String, w: Int): String = {
      val nspaces = (w - s.length) max 0
      s + (" " * nspaces)
    }
    
    def optline(name: String, text: String): String = {
      "%-2s".format("") + padRight(name, nameWidth) + "  %s%n".format(text)
    }
      
    val descriptions: String = {
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
    
    val header =
      """
Usage: %s [options] %s
        
""".format(program, anonName) +
optline(anonName, anonDesc) + """
Options:
"""

    private var currentArgs: List[String] = List()

    def usageErr(): Nothing = {
      val unprocessed = currentArgs match {
        case Nil => ""
        case _ => """
Unprocessed Arguments:
  """ + currentArgs.reduceRight({ _ + " " + _ }) + "%n".format()
      }
      print(header + descriptions + unprocessed)
      exit(1)
    }
    
    def process(args: Array[String]): T = {
      def loop(l: List[String]): List[String] = {
        currentArgs = l
        l match {
          case Nil => Nil
          case h :: t => opts.get(h) match {
            case None => l
            case Some(doit) => doit(); loop(t)
          }
        }
      }
      val err: PartialFunction[List[String], T] = { case _ => usageErr() }
      (anonDo orElse err)(loop(args.toList))
    }
  }
}