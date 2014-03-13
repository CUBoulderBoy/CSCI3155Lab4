object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
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
  
  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case (h1 :: h2) if (h == h1) => acc 
      case _ => h :: acc
    } 
  }
  
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match{
      case Some(a) => a :: t
      case None => h :: mapFirst(f)(t)
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 
    
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc
        case Node(l, d, r) => f(loop(loop(acc, l), r), d)
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = t.foldLeft(true, None: Option[Int]){
      (acc: (Boolean, Option[Int]), current: Int) => (acc, current) match{
        case ((false, Some(i)), _) => (false, Some(i))
      	case ((true, None), c) => (true, Some(c)) 
      	case ((b, Some(i)), c) => if (c < i) {
          (true, Some(c)) 
        } else (false, Some(i))
      } 
    }
    b
  }
  

  /* Type Inference */
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeInfer(env: Map[String,Typ], e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      //TypePrint
      case Print(e1) => typ(e1); TUndefined
      
      //TypeNumber
      case N(_) => TNumber
      
      //TypeBool
      case B(_) => TBool
      
      //TypeUndefined
      case Undefined => TUndefined
      
      //TypeString
      case S(_) => TString
      
      //TypeVar
      case Var(x) => env(x)
      
      //TypeConst
      case ConstDecl(x, e1, e2) => typeInfer(env + (x -> typ(e1)), e2)
      
      //TypeNeg
      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      
      //TypeNot
      case Unary(Not, e1) => typ(e1) match{
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      
      //TypeArith(Plus) & TypePlusString
      case Binary(Plus, e1, e2) => (typ(e1), typ(e2)) match{
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (e1got, e2got) => err(e1got, e1)
      }
      
      //TypeArith
      case Binary(bop @ (Minus|Times|Div), e1, e2) => (typ(e1), typ(e2)) match{
        case (TNumber, TNumber) => TNumber
        case (e1got, e2got) => err(e1got, e1)
      }
      
      //TypeEquality
      case Binary(bop @ (Eq|Ne), e1, e2) => (typ(e1), typ(e2)) match{
      	case (TFunction(a, b), _) => err(TFunction(a, b), e1)
      	case (_, TFunction(a, b)) => err(TFunction(a, b), e1)
      	case (e1got, e2got) => if (e1got == e2got) TBool else err(e1got, e1)
      }

      //TypeInequalityNumber & TypeInequalityString
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => (typ(e1), typ(e2)) match{
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool
        case (e1got, e2got) => err(e1got, e1)
      }
      
      //TypeAndOr
      case Binary(And|Or, e1, e2) =>(typ(e1), typ(e2)) match{
        case (TBool, TBool) => TBool
        case (e1got, e2got) => err(e1got, e1)
      }
      
      //TypeSeq
      case Binary(Seq, e1, e2) => typ(e2)

      //TypeIf
      case If(e1, e2, e3) => (typ(e1), typ(e2), typ(e3)) match{
        case (TBool, e2got, e3got) if (e2got == e3got) => e2got
        case (e1got, e2got, e3got) => err(e1got, e1)
      }
      
      //TypeFunction & TypeFunctionAnn
      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env + (f -> tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }
        
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = env1 ++ params
        
        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeInfer(env2, e1))
          case Some(tret) => TFunction(params, tret)
        }
      }
      
      //TypeCall
      case Call(e1, args) => typ(e1) match {
        case TFunction(params, tret) if (params.length == args.length) => {
          (params, args).zipped.foreach{
            case ((x, t), ex) => if (t != typ(ex)) err(t, ex)
          } 
        };
        tret
        case tgot => err(tgot, e1)
      }
      
      //TypeObject
      case Obj(fields) =>
        TObj(fields.mapValues((exp: Expr) => typ(exp)))
      
      //TypeGetField
      case GetField(e1, f) => typ(e1) match {
        case TObj(mappy) => mappy.get(f) match{
          case Some(t) => t
          case _ => err(TUndefined, e1)
        }
        case _ => err(typ(e1), e1)
      }
    }
  }
  
  
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
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) => ConstDecl(y, subst(e1), if (x == y) e2 else subst(e2))
      
      case Function(p, params, tann, e1) => {
        val ret =
        params.foldLeft(0: Int){
        	(ret: Int, c: (String, Typ)) => c match{
        	  case (x2, t) if (x == x2) => ret + 1
        	  case (x2, t) => ret}}
        if (p == Some(x) || (ret != 0)){
          Function(p, params, tann, e1)
        }
        else{
          Function(p, params, tann, subst(e1))
        }
      }
      
      case Call(e1, args) => Call(subst(e1), args.foldLeft(List(): List[Expr]){
            (acc: List[Expr], e2: Expr) => acc :+ subst(e2)})
      
      case Obj(fields) => Obj(fields.foldLeft(Map(): Map[String, Expr]){
            (acc: Map[String, Expr], m1: (String, Expr)) => m1 match{
              case (s1, e2) => acc + (s1 -> subst(e2))
          }
      })
      
      case GetField(e1, f) => GetField(subst(e1), f)
    }
  }
  
  def step(e: Expr): Expr = {
    require(!isValue(e))
    
    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      //DoPrint
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      
      //DoNeg
      case Unary(Neg, N(n1)) => N(- n1)
      
      //DoNot
      case Unary(Not, B(b1)) => B(! b1)
      
      //DoSeq
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      
      //DoPlusString
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      
      //DoArith
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
      
      //DoInequalityNumber & DoInequalityString
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      
      //DoEquality
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      
      //DoAndTrue & DoAndFalse
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      
      //DoOrTrue & DoOrFalse
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      
      //DoIfTrue & DoIfFalse
      case If(B(b1), e2, e3) => if (b1) e2 else e3
      
      //DoConstDecl
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)
      
      //DoCall & DoCallRec
      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, t, e1) => {
            //Zipped works by appending the first list with the second
            //A list of tupples and a list become List(Tuple, Val)
            val e1p = (params, args).zipped.foldRight(e1){
              (vars: ((String, Typ), Expr), acc: Expr) => (vars, acc) match {
                case (((x, t), v1), e1) => substitute(e1, v1, x)
              }
            }
            p match {
              case None => e1p
              case Some(x1) => substitute(e1p, Function(Some(x1), params, t, e1), x1)
            }
          }
          case _ => throw new StuckError(e)
        }
      
      //DoGetField & SearchGetField
      case GetField(v1, f) => v1 match{
        case Obj(mappy) => mappy.get(f) match {
          case Some(v1) if (isValue(v1)) => v1
          case Some(v1) => step(v1)
          case _ => throw new StuckError(e)
        }
        case _ => throw new StuckError(e)
      }
        
      /* Inductive Cases: Search Rules */
      //SearchPrint
      case Print(e1) => Print(step(e1))
      
      //SearchUnary
      case Unary(uop, e1) => Unary(uop, step(e1))
      
      //SearchBinary1
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      
      //SearchBinary2
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      
      //SearchIf
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      
      //SearchConst
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      
      //SearchCall1 & SearchCall2
      case Call(v1, args) => v1 match{
        case Function(None, params, t, e1) => {
          Call(Function(None, params, t, e1), args.foldLeft(List(): List[Expr]){
            (acc: List[Expr], e1: Expr) => if (isValue(e1)) {acc :+ e1} else {acc :+ step(e1)}
          })
        }
        case Function(Some(f), params, t, e1) => {
          Call(Function(Some(f), params, t, e1), args.foldLeft(List(): List[Expr]){
            (acc: List[Expr], e1: Expr) => if (isValue(e1)) {acc :+ e1} else {acc :+ step(e1)}
          })
        }
        case e1 => Call(step(e1), args)
      }
      
      //SearchObject
      case Obj(mappy) => Obj(mappy.foldLeft(Map(): Map[String, Expr]){
            (acc: Map[String, Expr], m1: (String, Expr)) => m1 match{
              case (s1, e1) if (isValue(e1)) => acc + (s1 -> e1)
              case (s1, e1) => acc + (s1 -> step(e1))
          }
      })
      
      /* Everything else is a stuck error. Should not happen if e is well-typed. */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  this.debug = true // comment this out or set to false if you don't want print debugging information
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val t = inferType(expr)
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }

}