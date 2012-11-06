package jsy.lab5
import scala.util.parsing.input.Positional

/**
 * @author Bor-Yuh Evan Chang
 */
object ast {
  sealed abstract class Expr extends Positional
  
  /* Variables */
  case class Var(x: String) extends Expr
  
  /* Declarations */
  case class Decl(mut: Mutability, x: String, e1: Expr, e2: Expr) extends Expr
  case class InterfaceDecl(tvar: String, tobj: Typ, e: Expr) extends Expr
  
  /* Literals and Values*/
  case class N(n: Double) extends Expr
  case class B(b: Boolean) extends Expr
  case object Undefined extends Expr
  case class S(s: String) extends Expr
  
  /* Unary and Binary Operators */
  case class Unary(uop: Uop, e1: Expr) extends Expr
  case class Binary(bop: Bop, e1: Expr, e2: Expr) extends Expr

  sealed abstract class Uop
  
  case object Neg extends Uop /* -e1 */
  case object Not extends Uop /* !e1 */

  sealed abstract class Bop
  
  case object Plus extends Bop /* e1 + e2 */
  case object Minus extends Bop /* e1 - e2 */
  case object Times extends Bop /* e1 * e2 */
  case object Div extends Bop /* e1 / e2 */
  case object Eq extends Bop /* e1 === e2 */
  case object Ne extends Bop /* e1 !=== e2 */
  case object Lt extends Bop /* e1 < e2 */
  case object Le extends Bop /* e1 <= e2 */
  case object Gt extends Bop /* e1 > e2 */
  case object Ge extends Bop /* e1 >= e2 */
  
  case object And extends Bop /* e1 && e2 */
  case object Or extends Bop /* e1 || e2 */
  
  case object Seq extends Bop /* , */
  
  /* Intraprocedural Control */
  case class If(e1: Expr, e2: Expr, e3: Expr) extends Expr
  
  /* Functions */
  case class Function(p: Option[String], params: List[(String,(PMode,Typ))], tann: Option[Typ], e1: Expr) extends Expr
  case class Call(e1: Expr, args: List[Expr]) extends Expr
  
  /* I/O */
  case class Print(e1: Expr) extends Expr 
  
  /* Objects */
  case class Obj(fields: Map[String, Expr]) extends Expr
  case class GetField(e1: Expr, f: String) extends Expr
  
  /* Addresses and Mutation */
  case class Assign(e1: Expr, e2: Expr) extends Expr
  case object Null extends Expr
  
  case class A(a: Int) extends Expr
  object A {
    /* Allocate addresses. */
    private var nextA: Int = 1
    def fresh(): A = {
      val r = A(nextA)
      nextA += 1;
      r
    }
  }
  
  case object Deref extends Uop /* *e1 */
  
  sealed abstract class Mutability
  case object Const extends Mutability
  case object Var extends Mutability
  
  sealed abstract class PMode
  case object PConst extends PMode
  case object PName extends PMode
  case object PVar extends PMode
  case object PRef extends PMode
  
  /* Casting */
  case class Cast(t: Typ) extends Uop
  
  /* Types */
  sealed abstract class Typ
  case object TNumber extends Typ
  case object TBool extends Typ
  case object TString extends Typ
  case object TUndefined extends Typ
  case object TNull extends Typ
  case class TFunction(params: List[(String,(PMode,Typ))], tret: Typ) extends Typ
  case class TObj(tfields: Map[String, Typ]) extends Typ
  case class TVar(tvar: String) extends Typ
  case class TInterface(tvar: String, t: Typ) extends Typ
  
  /* Define values. */
  def isValue(e: Expr): Boolean = e match {
    case N(_) | B(_) | Undefined | S(_) | Function(_, _, _, _) | A(_) | Null => true
    case _ => false
  }
  
  def isLExpr(e: Expr): Boolean = e match {
    case Var(_) | GetField(_, _) => true
    case _ => false
  }
  
  def isLValue(e: Expr): Boolean = e match {
    case Unary(Deref, A(_)) | GetField(A(_), _) => true
    case _ => false
  }
  

  def isBaseType(t: Typ): Boolean = t match {
    case TNumber | TBool | TString | TUndefined | TNull => true
    case _ => false
  }
  
  /*
   * Pretty-print values.
   * 
   * We do not override the toString method so that the abstract syntax can be printed
   * as is.
   */
  def pretty(v: Expr): String = {
    (v: @unchecked) match {
      case N(n) => n.toString
      case B(b) => b.toString
      case Undefined => "undefined"
      case S(s) => s
      case Function(p, _, _, _) =>
        "[Function%s]".format(p match { case None => "" case Some(s) => ": " + s })
      case Obj(fields) =>
        val pretty_fields =
          fields map {
            case (f, S(s)) => f + ": '" + s + "'"
            case (f, v) => f + ": " + pretty(v)
          } reduceRight {
            (s, acc) => s + ",\n  " + acc
          }
        "{ %s }".format(pretty_fields)
      case Null => "null"
      case A(i) => "0x%x".format(i)
    }
  }
  
  def pretty(m: Map[A,Expr], v: Expr): String = {
    (v: @unchecked) match {
      case a @ A(_) if m contains a => pretty(m, m(a))
      case Obj(fields) =>
        val pretty_fields =
          fields map {
            case (f, S(s)) => f + ": '" + s + "'"
            case (f, v) => f + ": " + pretty(m, v)
          } reduceRight {
            (s, acc) => s + ",\n  " + acc
          }
        "{ %s }".format(pretty_fields)
      case _ => pretty(v)
    }
  }
  
  def pretty(m: Mutability): String = m match {
    case Const => "const"
    case Var => "var"
  }
  
  /*
   * Pretty-print types.
   * 
   * We do not override the toString method so that the abstract syntax can be printed
   * as is.
   */
  def pretty(t: Typ): String = t match {
    case TNumber => "number"
    case TBool => "bool"
    case TString => "string"
    case TUndefined => "Undefined"
    case TFunction(params, tret) => {
      val pretty_params: Option[String] =
        params map { case (x,(mode,t)) => "%s %s: %s".format(pretty(mode), x, pretty(t)) } reduceRightOption {
          (s, acc) => s + ", " + acc
        }
      "(%s) => %s".format(pretty_params.getOrElse(""), pretty(tret))
    }
    case TObj(tfields) =>
      val pretty_fields: Option[String] =
        tfields map { case (f,t) => "%s: %s".format(f, pretty(t)) } reduceRightOption {
          (s, acc) => s + "; " + acc
        }
      "{ %s }".format(pretty_fields.getOrElse(""))
    case TNull => "Null"
    case TVar(tvar) => tvar
    case TInterface(tvar, t1) => "Interface %s %s".format(tvar, pretty(t1))
  }
  
  def pretty(m: PMode): String = m match {
    case PConst => "const"
    case PName => "name"
    case PVar => "var"
    case PRef => "ref"
  }
  
  /* Get the free variables of e. */
  def freeVarsVar(e: Expr): Set[Var] = e match {
    case vr @ Var(x) => Set(vr)
    case Decl(_, x, e1, e2) => freeVarsVar(e1) | (freeVarsVar(e2) - Var(x))
    case Function(p, params, _, e1) => freeVarsVar(e1) -- (params map { case (x, _) => Var(x) }) -- (p map { x => Var(x) })
    case N(_) | B(_) | Undefined | S(_) | Null | A(_) => Set.empty
    case Unary(_, e1) => freeVarsVar(e1)
    case Binary(_, e1, e2) => freeVarsVar(e1) | freeVarsVar(e2)
    case If (e1, e2, e3) => freeVarsVar(e1) | freeVarsVar(e2) | freeVarsVar(e3)
    case Call(e1, args) => freeVarsVar(e1) | args.foldLeft(Set.empty: Set[Var]){ ((acc: Set[Var], ei) => acc | freeVarsVar(ei)) }
    case Print(e1) => freeVarsVar(e1)
    case Obj(fields) => fields.foldLeft(Set.empty: Set[Var])({ case (acc, (_, ei)) => acc | freeVarsVar(ei) })
    case GetField(e1, _) => freeVarsVar(e1)
    case Assign(e1, e2) => freeVarsVar(e1) | freeVarsVar(e2)
    case InterfaceDecl(_, _, e1) => freeVarsVar(e1)
  }
  def freeVars(e: Expr): Set[String] = freeVarsVar(e) map { case Var(x) => x }
  
  /* Check closed expressions. */
  class UnboundVariableError(x: Var) extends Exception {
    override def toString =
      Parser.formatErrorMessage(x.pos, "UnboundVariableError", "unbound variable %s".format(x.x))
  }
  
  def closed(e: Expr): Boolean = freeVarsVar(e).isEmpty
  def checkClosed(e: Expr): Unit = {
    freeVarsVar(e).headOption.foreach { x => throw new UnboundVariableError(x) }
  }

  /* Transformation visitor. */
  def transformVisitor(visitant: (Expr => Expr) => PartialFunction[Expr, Expr])(e: Expr): Expr = {
    def tr(e: Expr): Expr = {
      val f = visitant(tr).orElse[Expr,Expr] {
        case Var(_) | N(_) | B(_) | Undefined | S(_) | Null | A(_) => e
        case Print(e1) => Print(tr(e1))
        case Unary(uop, e1) => Unary(uop, tr(e1))
        case Binary(bop, e1, e2) => Binary(bop, tr(e1), tr(e2))
        case If(e1, e2, e3) => If(tr(e1), tr(e2), tr(e3))
        case Decl(mut, y, e1, e2) => Decl(mut, y, tr(e1), tr(e2))
        case Function(p, params, retty, e1) => Function(p, params, retty, tr(e1))
        case Call(e1, args) => Call(tr(e1), args map tr)
        case Obj(fields) => Obj(fields map { case (f,e) => (f, tr(e)) })
        case GetField(e1, f) => GetField(tr(e1), f)
        case Assign(e1, e2) => Assign(tr(e1), tr(e2))
        case InterfaceDecl(tvar, t, e1) => InterfaceDecl(tvar, t, tr(e1))
      }
      f(e)
    }
    tr(e)
  }
  
  /* Substitute in type t replacing uses of type variable tvar with type tp */
  def typSubstitute(t: Typ, tp: Typ, tvar: String): Typ = {
    def subst(t: Typ): Typ = t match {
      case TNumber | TBool | TString | TUndefined | TNull => t
      case TFunction(params, rt) =>
        TFunction(params map { case (x,(mode,t)) => (x,(mode,subst(t)))}, subst(rt))
      case TObj(fields) => TObj(fields mapValues subst)
      case TVar(tvarp) => if (tvar == tvarp) tp else t
      case TInterface(tvarp, t1) =>
        if (tvar == tvarp) t // tvar shadowed by tvarp
        else TInterface(tvarp, subst(t1))
    }
    subst(t)
  }
  
  /* Substitute in an expression e all uses of type variable tvar with type tp */
  def typSubstituteExpr(tp: Typ, tvar: String, e: Expr): Expr = {
    def tysubst(t: Typ): Typ = typSubstitute(t, tp, tvar)
    def subst(tr: Expr => Expr): PartialFunction[Expr, Expr] = {
      case Unary(Cast(t), e1) => Unary(Cast(tysubst(t)), tr(e1))
      case Function(p, params, retty, e1) =>
        Function(p, params map { case (x,(mode,t)) => (x,(mode,tysubst(t))) }, retty map tysubst, tr(e1))
      case InterfaceDecl(_, _, _) => throw new IllegalArgumentException
    }
    transformVisitor(subst)(e)
  }
   
  /*
   * Dynamic Type Error exception.  Throw this exception to signal a dynamic
   * type error.
   * 
   *   throw new DynamicTypeError(e)
   * 
   */
  class DynamicTypeError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "DynamicTypeError", "in evaluating " + e)
  }
  
  /*
   * Null Dereference Error exception.  Throw this exception to signal a null
   * pointer dereference error.
   * 
   *   throw new NullDereferenceError(e)
   * 
   */
  class NullDereferenceError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "NullDereferenceError", "in evaluating " + e)
  }
  
  /*
   * Static Type Error exception.  Throw this exception to signal a static
   * type error.
   * 
   *   throw new StaticTypeError(tbad, esub, e)
   * 
   */
  class StaticTypeError(tbad: Typ, esub: Expr, e: Expr) extends Exception {
    override def toString =
      Parser.formatErrorMessage(esub.pos, "StaticTypeError", "invalid type %s for sub-expression %s in %s".format(pretty(tbad), esub, e))
  }
  
  /*
   * Stuck Type Error exception.  Throw this exception to signal getting
   * stuck in evaluation.  This exception should not get raised if
   * evaluating a well-typed expression.
   * 
   *   throw new StuckError(e)
   * 
   */
  class StuckError(e: Expr) extends Exception {
    override def toString = Parser.formatErrorMessage(e.pos, "StuckError", "in evaluating " + e)
  }
  
}