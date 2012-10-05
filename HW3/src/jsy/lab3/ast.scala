/**
 * Version History:
 *   0.2 (09/18/2012): Changed printing of AST nodes.
 *   0.1 (09/07/2012): Initial release.
 */
package jsy.lab3

/**
 * @author Bor-Yuh Evan Chang
 */
object ast {
  sealed abstract class Expr
  
  /* Variables */
  case class Var(x: String) extends Expr
  
  /* Declarations */
  case class ConstDecl(x: String, e1: Expr, e2: Expr) extends Expr
  
  /* Literals and Values*/
  case class N(n: Double) extends Expr
  case class B(b: Boolean) extends Expr
  case object Undefined extends Expr
  case class S(s: String) extends Expr
  
  /* Unary and Binary Operators */
  case class Unary(uop: Uop, e1: Expr) extends Expr
  case class Binary(bop: Bop, e1: Expr, e2: Expr) extends Expr

  sealed abstract class Uop
  
  case object Neg extends Uop /* - */
  case object Not extends Uop /* ! */

  sealed abstract class Bop
  
  case object Plus extends Bop /* + */
  case object Minus extends Bop /* - */
  case object Times extends Bop /* * */
  case object Div extends Bop /* / */
  case object Eq extends Bop /* === */
  case object Ne extends Bop /* !=== */
  case object Lt extends Bop /* < */
  case object Le extends Bop /* <= */
  case object Gt extends Bop /* > */
  case object Ge extends Bop /* >= */
  
  case object And extends Bop /* && */
  case object Or extends Bop /* || */
  
  case object Seq extends Bop /* , */
  
  /* Intraprocedural Control */
  case class If(e1: Expr, e2: Expr, e3: Expr) extends Expr
  
  /* Functions */
  case class Function(p: Option[String], x: String, e1: Expr) extends Expr
  case class Call(e1: Expr, e2: Expr) extends Expr
  
  /* I/O */
  case class Print(e1: Expr) extends Expr 
  
  /* Define values. */
  def isValue(e: Expr): Boolean = e match {
    case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => true
    case _ => false
  }
  
  /*
   * Pretty-print values.
   * 
   * We do not override the toString method so that the abstract syntax can be printed
   * as is.
   */
  def pretty(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => n.toString
      case B(b) => b.toString
      case Undefined => "undefined"
      case S(s) => "\"%s\"".format(s)
      case Function(p, _, _) =>
        "[Function%s]".format(p match { case None => "" case Some(s) => ": " + s })
    }
  }
  
  /*
   * Dynamic Type Error exception.  Throw this exception to signal a dynamic type error.
   * 
   *   throw new DynamicTypeError(e)
   * 
   */
  class DynamicTypeError(e: Expr) extends Exception {
    override def toString = "TypeErrror: in expression " + e
  }
  
}