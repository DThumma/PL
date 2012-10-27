object Lab4_pekl2737 {
  import jsy.lab4.ast._
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: CSEL Family
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
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if(h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match{
      case Nil    => h :: acc
      case h1 :: t => if(h == h1) acc else h :: acc
    }
  }
  
  def testCompress(compress: List[Int] => List[Int]): Boolean = {
//    println(compress(List(1, 2, 2, 3, 3, 3)))
    compress(List(1, 2, 2, 3, 3, 3)) == List(1, 2, 3)
    //val stuff = compress(List(1, 2, 2, 3, 3, 3))
  }
  assert(testCompress(compressRec))
  assert(testCompress(compressFold))
  
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case Some(x) => x :: t 
      case None => h :: mapFirst(f)(t)
    }
  }
  
  def testMapFirst(mapFirst: (Int => Option[Int]) => List[Int] => List[Int]): Boolean =
    mapFirst((i: Int) => if (i < 0) Some(-i) else None)(List(1, 2, -3, 4, -5)) == List(1, 2, 3, 4, -5)
  assert(testMapFirst(mapFirst))
  
  /* Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 

// ############## WE DON'T NEED TO IMPLEMENT THIS, BUT GET EXTRA CREDIT IF WE DO ##########################
//    def map(f: Int => Int): Tree = this match {
//      case Empty => Empty
//      case Node(l, d, r) => (l, d, r) match {
//        case (Empty, d, Empty) => map
//        case (l, d, Empty) => map(f(d))
//        
//      }
//    }
// ########################################################################################################
   
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc
        case Node(l, d, r) => loop(f(loop(acc, l), d), r)         
      }
      loop(z, this)
    }


  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
// ############## WE DON'T NEED TO IMPLEMENT THIS, BUT GET EXTRA CREDIT IF WE DO ##########################
//  def incr(t: Tree): Tree = t.map(i => i + 1)
//  //def incr(t: SearchTree): SearchTree = t.map{ i => i + 1 }
//  //def incr(t: SearchTree): SearchTree = t.map{ _ + 1 } // using placeholder notation
//  
//  def testIncr(incr: Tree => Tree): Boolean =
//    incr(treeFromList(List(1,2,3))) == treeFromList(List(2,3,4))
//  //assert(testIncr(incr))
// ########################################################################################################
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def testSum(sum: Tree => Int): Boolean = {
    val l = List(3, 2, 3)
    sum(treeFromList(l)) == 8
  }
  assert(testSum(sum))
  
  def strictlyOrdered(t: Tree): Boolean = {    
    val (b, _) = t.foldLeft((true, None: Option[Int])){
      (acc, d) => acc match{
        case (b1, None) => (b1, Some(d))
        case (b2, nextInt) =>(nextInt.get < d && b2, Some(d)) 
      }
    }
    b
  }


  
  def testStrictlyOrdered(strictlyOrdered: Tree => Boolean): Boolean =
    !strictlyOrdered(treeFromList(List(1,1,2)))
  //assert(testStrictlyOrdered(strictlyOrdered))
  
  /* Type Inference */
  
  def hasFunctionTyp(t: Typ): Boolean = t match {
   case TFunction(_, _) => true
   case TObj(fieldtypes) => fieldtypes exists { case (_, t) => hasFunctionTyp(t) }
   case _ => false
 }
  
  def hasUndefinedTyp(t: Typ): Boolean = t match {
    case TUndefined => true
    case TObj(fieldtypes) => fieldtypes exists { case(_, t) => hasFunctionTyp(t) }
    case _ => false
  }

 def typeInfer(env: Map[String,Typ], e: Expr): Typ = {
   def typ(e1: Expr) = typeInfer(env, e1)
   def err[T](tgot: Typ, e1: Expr): T = throw new StaticTypeError(tgot, e1, e)
   e match {
     case Print(e1) => typ(e1); TUndefined
     case N(_) => TNumber
     case B(_) => TBool
     case Undefined => TUndefined
     case S(_) => TString
     case Var(x) => env(x)
     case ConstDecl(x, e1, e2) => typeInfer(env + (x -> typ(e1)), e2)
     case Obj(params) => TObj(params.map{ case (k,v) => (k,typ(v)) })
     case Binary(op, e1, e2) => op match {
         case Plus => (typ(e1), typ(e2)) match {
          case (TNumber, TNumber) => TNumber
          case (TString, TString) => TString
          case (tgot: Typ, _) if(tgot != TNumber && tgot != TString) => err(tgot, e1)
          case (_, tgot: Typ) => err(tgot, e2)
         }
         case Minus | Times | Div  => (typ(e1), typ(e2)) match {
           case (TNumber, TNumber) => TNumber
           case (tgot: Typ, _) if(tgot != TNumber) => err(tgot, e1)
           case (_, tgot: Typ) => err(tgot, e2)
         }
         case Lt | Le | Gt | Ge => (typ(e1), typ(e2)) match {
	       case (TNumber, TNumber) => TBool
	       case (TString, TString) => TBool
	       case (tgot: Typ, _) if(tgot != TNumber && tgot != TString) => err(tgot, e1)
	       case (_, tgot: Typ) => err(tgot, e2)
       }
       case Eq | Ne => typ(e1) match {
         case tgot if (hasFunctionTyp(tgot)) => err(tgot, e1)
         case _ => typ(e2) match {
           case tgot if (hasFunctionTyp(tgot)) => err(tgot, e2)
//           case tgot if (hasUndefinedTyp(tgot)) => err(tgot, e2)
           case _ => if(typ(e1) == typ(e2)) TBool else err(typ(e2), e2)
         }
       }
       case Seq => typ(e1); typ(e2)
       case And | Or => (typ(e1), typ(e2)) match {
         case (TBool, TBool) => TBool
         case (_, tgot) => err(tgot, e2)
       }
       case _ => throw new UnsupportedOperationException
     }
     case Unary(Neg, e1) => typ(e1) match {
       case TNumber => TNumber
       case tgot => err(tgot, e1)
     }
     case Unary(Not, e1) => typ(e1) match {
       case TBool => TBool
       case tgot => err(tgot, e1)
     }
     case If(e1, e2, e3) => (typ(e1),typ(e2),typ(e3)) match {
       case (TBool, t1, t2) => if(t1 == t2) t1 else err(t2, e3)
       //case TBool => if (true) typ(e2) else typ(e3) // Replace with above
       case (tgot,_,_) => err(tgot, e1)
     }
     case Call(e1, args) => typ(e1) match{
       case TFunction(params, rett) if (params.length == args.length) => {
         //zip and check parameter types
         val pairs = params zip args
         pairs.foreach{
           pair => val (v1, v2) = pair
           if (v1._2 != typ(v2)) err(typ(v2), v2) else typ(v2)
         };
         rett
         }         
       case tgot => err(tgot, e1)
     }
     case GetField(expr, f) => {
       val e = typ(expr) 
       e match {
         case TObj(fields) => fields.get(f) match {
           case None => err(e, expr)
           case Some(v) => v
         }
         case _ => err(e, expr)
       }
     }
     case Function(p, params, tann, e1) => {
       // Bind to env1 an environment that extends env with an appropriate binding if
       // the function is potentially recursive.
       val env1 = (p, tann) match {
         case (Some(f), Some(rt)) =>
           val tprime = TFunction(params, rt)
           env + (f -> tprime)
         case (None, _) => env
         case _ => err(TUndefined, e1)
       }
       // Bind to env2 an environment that extends env1 with bindings for params.
       // take what we got from env1 and add all the parameter types '++' adds a whole collection of key value pairs
       val env2 = params.foldLeft(env1) {
         case (acc, (xi, ti)) => acc + (xi -> ti)
       }
       // Match on whether the return type is specified.
       tann match {
         case None => {
          val tau = typeInfer(env2,e1)
          val tauPrime = TFunction(params, tau)
          tauPrime
         }
         case Some(rt) => {
           val tau = typeInfer(env2, e1)
           val tauPrime = TFunction(params, tau)
           if(tauPrime != TFunction(params, rt)) err(tau, e1) else TFunction(params, rt)
          }
        }
      }
      case _ => throw new UnsupportedOperationException
    }
  }  
  def inferType(e: Expr): Typ = typeInfer(Map.empty, e)
  
  /* Small-Step Interpreter */
  
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    
    def subst(e: Expr): Expr = substitute(e, v, x)
    
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Call(e1, args) => Call(subst(e1), args map subst)
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) =>
        ConstDecl(y, subst(e1), if (x == y) e2 else subst(e2))
      case GetField(e1, f) => GetField(subst(e1), f)
      case _ => println("the following fields were not found");println(e); throw new UnsupportedOperationException
    }
  }
  
  def step(e: Expr): Expr = {
    require(!isValue(e))
    
    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, N(n1)) => N(- n1)
      case Unary(Not, B(b1)) => B(! b1)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2))   => N(n1 / n2)
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      /*** Fill-in more cases here. ***/
      case If(B(true), e2, e3)  => e2
      case If(B(false), e2, e3) => e3
      case GetField(Obj(fields), f) if (fields.forall {
        case (_, vi) => isValue(vi) }) => fields.get(f) match {
          case None => throw new StuckError(e)
          case Some(v) => v
        }
      case Call(Function(None, params, _, e1), args) if (args.foldLeft(true)((truth, x) => truth && isValue(x))) => {
        val zippedList = params zip args
        zippedList.foldLeft(e1){(express, x) => x match {
            case((name, _), value) => substitute(express, value, name)
          }
        } 
      }
      case Call(f1 @ Function(Some(f), params, _, e1), args) if (args.foldLeft(true)((truth, x) => truth && isValue(x))) => {
        val zippedList = params zip args
        zippedList.foldLeft(e1){(express, x) => x match {
            case((name, _), value) => substitute(express, value, name); substitute(express, f1, f)
          }
        } 
      }
        
      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      /*** Fill-in more cases here. ***/
      case Call(v1 @ Function(_, _, _, _), args) => {
        val args1 = mapFirst{(a:Expr) => if(!isValue(a)) Some(step(a)) else None}(args)
        Call(v1, args1)
      }
      case Call(e1, args) => Call(step(e1), args)
//      case Call(v1, args) => v1 match {
//        case Function(_, _, _, _) => {
//          val args1 = mapFirst{(a:Expr) => if(!isValue(a)) Some(step(a)) else None}(args)
//          Call(v1, args1)
//        }
//        case GetField(expr, f) => 
//        case _ => println(v1); throw new UnsupportedOperationException
//      }
      case GetField(e1, f) => GetField(step(e1), f)
      case Obj(f) => {
        val fList = f.toList
        def newFunction(arg: (String, Expr)): Option[(String, Expr)] = {
          arg match {
            case (s, e1) => if(!isValue(e1)) Some(s, step(e1)) else None
          }
        }
        val newList = mapFirst(newFunction)(fList)
        val fMap = newList.toMap
        Obj(fMap)
      }
      
      /* Everything else is a stuck error. */
      case _ => println(e);throw new StuckError(e)
    }
  }

  def iterateStep(e: Expr): Expr =
    if (isValue(e)) e else iterateStep(step(e))
    
}