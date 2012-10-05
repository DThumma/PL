/**
 *
 */
package jsy.lab2

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
  case class N(n: Double) extends Expr {
    override def toString: String = this.n.toString
  }
  case class B(b: Boolean) extends Expr {
    override def toString: String = this.b.toString
  }
  case object Undefined extends Expr {
    override def toString: String = "undefined"
  }
  
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
  
  /* I/O */
  case class Print(e1: Expr) extends Expr 
  
  /* Define values. */
  def isValue(e: Expr): Boolean = e match {
    case N(_) | B(_) | Undefined => true
    case _ => false
  }
  
}