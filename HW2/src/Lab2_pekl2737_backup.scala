object Lab2_pekl2737_backup {
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
   * <Peter Klipfel>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace 'YourIdentiKey' in the object name above with your IdentiKey.
   * 
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
   case Undefined => Double.NaN
   case null => 0.0
   case B(true) => 1.0
   case B(false) => 0.0
   case N(n) => n
   case _ => throw new UnsupportedOperationException
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case B(b) => b
      case Undefined => false
      case null => false
      case N(0.0) => false
      case N(Double.NaN) => false
      case _ => true
    }
  }

  def eval(env: Env, e: Expr): Expr = {
    e match {
      /* Base Cases */
      case _ if (isValue(e)) => e
      
      /* Inductive Cases */
      case Print(e1) => {
       println(eval(env, e1))
       Undefined 
      }
      
      case Var(x) => get(env, x)
      
      case ConstDecl(x, e1, e2) => {
        val v1 = eval(env, e1)
        val envx = extend(env, x, v1)
        eval(envx, e2)
      }       
      
      /* if statement */
      case If(e1, e2, e3) => {
        if( toBoolean(eval(env, e1)) ){
          eval(env, e2)
        }
        else{
          eval(env, e3)
        }
      }
      
      /* Mathematics */
      case Binary(Plus,e1,e2) => N(toNumber(eval(env,e1)) + toNumber(eval(env,e2)))    /* + */
      case Binary(Minus,e1,e2) => N(toNumber(eval(env,e1)) - toNumber(eval(env,e2)))   /* - */
      case Binary(Times,e1,e2) => N(toNumber(eval(env, e1)) * toNumber(eval(env, e2))) /* * */
      case Binary(Div,e1,e2) => N(toNumber(eval(env, e1)) / toNumber(eval(env, e2)))   /* / */
      
      case Binary(Lt,e1,e2) => B(toNumber(eval(env, e1)) < toNumber(eval(env, e2))) /* < */
      case Binary(Le,e1,e2) => B(toNumber(eval(env, e1)) <= toNumber(eval(env, e2))) /* <= */
      case Binary(Gt,e1,e2) => B(toNumber(eval(env, e1)) > toNumber(eval(env, e2))) /* > */
      case Binary(Ge,e1,e2) => B(toNumber(eval(env, e1)) >= toNumber(eval(env, e2))) /* >= */
      
      /* Boolean Syntax */
      case Binary(Eq,e1,e2) => B(toBoolean(eval(env, e1)) == toBoolean(eval(env, e2))) /* === */
      case Binary(Ne,e1,e2) => B(toBoolean(eval(env, e1)) != toBoolean(eval(env, e2))) /* !== */
      case Binary(And,e1,e2) => B(toBoolean(eval(env, e1)) && toBoolean(eval(env, e2)))
      case Binary(Or,e1,e2) => B(toBoolean(eval(env, e1)) || toBoolean(eval(env, e2)))
      
      case Binary(seq, e1, e2) => {
        val _= eval(env, e1)
        eval(env, e2)
      }
      
      /* Unary */
      case Unary(Not, e1) => {
       B(!toBoolean(eval(env,e1)))
      }
      case Unary(Neg, e1) => {
        N(-1*toNumber(eval(env, e1)))
      }
      case _ => throw new UnsupportedOperationException
    }
  }
      
  def evaluate(e: Expr): Expr = eval(emp, e)
    
}