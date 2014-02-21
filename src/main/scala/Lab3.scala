object Lab3 extends jsy.util.JsyApplication {
  import jsy.lab3.ast._
  
  /*
   * CSCI 3155: Lab 3 
   * Samuel Volin	
   * 
   * Partner: Cris Salazar
   * Collaborators: Alex Tsankov
   * 
   * ***Functions are Values***
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
      case N(n) => n
      case B(false) => 0
      case B(true) => 1
      case Undefined => Double.NaN
      case S(s) => try s.toDouble catch { case _: Throwable => Double.NaN }
      case Function(_, _, _) => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) if (n compare 0.0) == 0 || (n compare -0.0) == 0 || n.isNaN => false
      case N(_) => true
      case B(b) => b
      case Undefined => false
      case S("") => false
      case S(_) => true
      case Function(_, _, _) => true
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case B(b) => b.toString
      case Undefined => "undefined"
      case S(s) => s
      case Function(_, _, _) => "function"
    }
  }

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   */
  def inequalityVal(bop: Bop, e1: Expr, e2: Expr): Boolean = {
	require(isValue(e1))
	require(isValue(e2))
	require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (e1, e2) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case _ =>
        val (n1, n2) = (toNumber(e1), toNumber(e2))
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }


  /* Big-Step Interpreter with Dynamic Scoping */
  
  /*
   * This code is a reference implementation of JavaScripty without
   * strings and functions (i.e., Lab 2).  You are to welcome to
   * replace it with your code from Lab 2.
   */
  def eval(env: Env, e: Expr): Expr = {
    def eToN(e: Expr): Double = toNumber(eval(env, e))
    def eToB(e: Expr): Boolean = toBoolean(eval(env, e))
    def eToVal(e: Expr): Expr = eval(env, e)
    e match {
      /* Base Cases */
      case _ if isValue(e) => e
      case Var(x) => get(env, x)
      
      /* Inductive Cases */
      case Print(e1) => println(pretty(eval(env, e1))); Undefined
      
      case Unary(Neg, e1) => N(- eToN(e1))
      case Unary(Not, e1) => B(! eToB(e1))
      
      case Binary(Plus, e1, e2) => (eToVal(e1), eToVal(e2)) match {
        case (S(s1), e2) => S(s1 + toStr(e2))
        case (e1, S(s2)) => S(toStr(e1) + s2)
        case (e1, e2) => N(toNumber(e1) + toNumber(e2))
      }      
      case Binary(Minus, e1, e2) => N(eToN(e1) - eToN(e2))
      case Binary(Times, e1, e2) => N(eToN(e1) * eToN(e2))
      case Binary(Div, e1, e2) => N(eToN(e1) / eToN(e2))
      
      case Binary(Eq, e1, e2) => e1 match{
        case Function(x, y, z) => throw new DynamicTypeError(e)
		case _ => e2 match{
		  case Function(x, y, z) => throw new DynamicTypeError(e)
		  case _ => B(eToVal(e1) == eToVal(e2))
		}	
      }
      
      case Binary(Ne, e1, e2) => e1 match{
        case Function(x, y, z) => throw new DynamicTypeError(e)
		case _ => e2 match{
		  case Function(x, y, z) => throw new DynamicTypeError(e)
		  case _ => B(eToVal(e1) != eToVal(e2))
		}	
      }
      case Binary(bop @ (Lt|Le|Gt|Ge), e1, e2) => B(inequalityVal(bop, eToVal(e1), eToVal(e2)))
      
      case Binary(And, e1, e2) => 
        val v1 = eToVal(e1)
        if (toBoolean(v1)) eToVal(e2) else e1
      case Binary(Or, e1, e2) =>
        val v1 = eToVal(e1)
        if (toBoolean(v1)) e1 else eToVal(e2)
      
      case Binary(Seq, e1, e2) => eToVal(e1); eToVal(e2)
      
      case If(e1, e2, e3) => if (eToB(e1)) eToVal(e2) else eToVal(e3)
      
      case ConstDecl(x, e1, e2) => eval(extend(env, x, eToVal(e1)), e2)
      //
       case Call(e1, e2) =>  {
	  val v1 = eToVal(e1)
	  println("BUTTS" + v1);
		v1 match{
		  	//case Function(Some(p),x,e3) => eval(extend(env, x, eToVal(e2)), e3)
	    	case Function(None,x,e3) => eval(extend(env, x, eval(env, e2)), e3)
			case Function(Some(p),x,e3) => eval(extend(extend(env, p, v1), x, eval(env, e2)), e3)
			
			case _ => throw new DynamicTypeError(e)
		}
	  }
      
      
      case _ => throw new UnsupportedOperationException
    }
  }
    
  //Function(p, x, e) p is the function name (optional)
  //x is the argument passed in,
  //e is the function body
  
  

  /* Small-Step Interpreter with Static Scoping */
  //we like static scoping
  //for every instance of x, replace it with v in the expression e
  //in e, replace all v with x
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    /* Simple helper that calls substitute on an expression
     * with the input value v and variable name x. */
    
    /* Body */
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      //if e is a function and contains the string x, return it
      //otherwise substitute into the function
      case Function(p, s, e1) => if((Some(x) == p) || (x ==s)) return e else return Function(p,s, substitute(e1, v, x))
      case Binary(op, e1, e2) => op match{
        case (Eq|Ne) => e1 match {
          case Function(x,y,z) => throw new DynamicTypeError(e)
          case _ => return Binary(op, substitute(e1, v,  x), substitute(e2, v ,x)); //
        }
        case _ => return Binary(op, substitute(e1, v,  x), substitute(e2, v ,x)); //
      }
      case Unary(op, e1) => return Unary(op, substitute(e1,v,x))
      case Call(e1, e2) => return Call(substitute(e1, v,  x), substitute(e2, v ,x))
      case If(e1, e2, e3) => return If(substitute(e1, v, x), substitute(e2, v ,x), substitute(e3, v ,x))
      case Print(e1) => Print(substitute(e1, v ,x))
      case Var(t) => if(t == x) return v else e
      case ConstDecl(y,e1, e2) => ConstDecl(y, substitute(e1, v, x), if (x == y) e2 else substitute(e2, v, x))
      //case ConstDecl(t, e1, e2) => if(t == x) return ConstDecl(t, v, substitute(e2, v ,x)) else return ConstDecl(t, substitute(e1, v ,x), substitute(e2, v ,x))
      case _ => throw new UnsupportedOperationException
    }
  }
    
  def step(e: Expr): Expr = {
    println("XXX"+e+"XXX")
    
    e match {
      /* Base Cases: Do Rules */
      case Print(e1) if isValue(e1) => println(pretty(e1)); Undefined
      case Print(e1) => Print(step(e1))
        // ****** Your cases here
      //Unary
      case Unary(op, e1) if (isValue(e1)) => op match{
		case Neg => return N( - toNumber(e1))
		case Not => return B( ! toBoolean(e1))
	  }
      case Unary(op, e1) => Unary(op, step(e1))
	  //Binary
	  case Binary(op, e1, e2) if (isValue(e1) && isValue(e2)) => op match{
	  	case Plus => (e1, e2) match {
			//first argument string
			case(S(s1),e2) => return S(s1 + toStr(e2))
			//second argument string
			case(e1, S(s2)) => return S(toStr(e1) + s2)
			//default
			case (_,_) => return N(toNumber(e1)+toNumber(e2))
		}
	  	case Minus => return N(toNumber(e1)-toNumber(e2))
		case Times => return N(toNumber(e1) * toNumber(e2))
		case Div => return N(toNumber(e1) / toNumber(e2))

		case Eq => (e1, e2) match {
			case (Function(x, y, z), e2) => throw new DynamicTypeError(e)
			case (e1, Function(x, y, z)) => throw new DynamicTypeError(e)
			//case (S(v1), e2) => return B( toNumber(e1) == toNumber(e2) ) //inequalitynumber1
			//case (e1, S(v2)) => return B( toNumber(e1) == toNumber(e2) ) //inequalitynumer2
			case (_,_) => return B( e1 == e2 )
		}
		case Ne => (e1, e2) match {
			case (Function(x, y, z), e2) => throw new DynamicTypeError(e)
			case (e1, Function(x, y, z)) => throw new DynamicTypeError(e)
			//case (S(v1), e2) => return B( toNumber(e1) == toNumber(e2) ) //inequalitynumber1
			//case (e1, S(v2)) => return B( toNumber(e1) == toNumber(e2) ) //inequalitynumer2
			case (_,_) => return B( e1 != e2 )
		}

		case Lt => (e1, e2) match { // >
		  case(S(s1), S(s2)) => B( s1 < s2 )
			case(S(s1),e2) => B( toNumber(e1) < toNumber(e2) )
			case(e1, S(s2)) => B( toNumber(e1) < toNumber(e2) )
			
			case (_,_) => B( toNumber(e1) < toNumber(e2) )
			}
		case Gt => (e1, e2) match { // >
			case(S(s1), S(s2)) => B( s1 > s2 )
			case(S(s1),e2) => B( toNumber(e1) > toNumber(e2) )
			case(e1, S(s2)) => B( toNumber(e1) > toNumber(e2) )
			
			case (_,_) => B( toNumber(e1) > toNumber(e2) )
			}
		case Le => (e1, e2) match { // <=
		  case(S(s1), S(s2)) => B( s1 <= s2 )
			case(S(s1),e2) => B( toNumber(e1) <= toNumber(e2) )
			case(e1, S(s2)) => B( toNumber(e1) <= toNumber(e2) )
			
			case (_,_) => B( toNumber(e1) <= toNumber(e2) )
			}

		case Ge => (e1, e2) match { // >=
		  case(S(s1), S(s2)) => B( s1 >= s2 )
			case(S(s1),e2) => B( toNumber(e1) >= toNumber(e2) )
			case(e1, S(s2)) => B( toNumber(e1) >= toNumber(e2) )
			
			case (_,_) => B( toNumber(e1) >= toNumber(e2) )
			}
		case And  => if (toBoolean(e1)) return e2 else return e1
		//if first argument true return true else return second argument
		case Or  => if (toBoolean(e1)) return e1 else return e2
	  }
	  //case Binary(Seq, e1, e2) if (isValue(e1)) => e2
	  case Binary(op, e1, e2) if (isValue(e1)) =>  op match {
	    case Seq => e2
	    //if first argument true return second argument else return false
		case And  => if (toBoolean(e1)) return e2 else return e1
		//if first argument true return true else return second argument
		case Or  => if (toBoolean(e1)) return e1 else return e2
	    case _ => Binary(op, e1, step(e2))
	  }
      case Binary(op, e1, e2) => Binary(op, step(e1), e2)
	  
	  case If(e1, e2, e3) if (isValue(e1)) => {println("IFSTEP"); if (toBoolean(e1)) return e2 else return e3}
	  case If(e1, e2, e3) => If(step(e1), e2, e3)
	  
	  case ConstDecl(x, e1, e2) if (isValue(e1)) => return substitute(e2, e1, x)
	  case ConstDecl(x, e1, e2) => return ConstDecl(x, step(e1), e2)
      case Call(e1, e2) if ((isValue(e1) && isValue(e2))) => e1 match {
        case Function(Some(p), x, e3 ) => return substitute(substitute(e3, e1, p),e2,x);
        case Function(None, x, e3 ) => return substitute(e3, e2, x)
        case _ => throw new DynamicTypeError(e);
      }
      
      case Call(v1, e2) if(isValue(v1)) => v1 match {
        case Function(x, y, z) => Call(v1, step(e2))
        case _ => throw new DynamicTypeError(e)
      }
      
      case Call(e1, e2) => Call(step(e1), e2)

            
      
      /* Cases that should never match. Your cases above should ensure this. */
      case Var(_) => throw new AssertionError("Gremlins: internal error, not closed expression.")
      case N(_) | B(_) | Undefined | S(_) | Function(_, _, _) => throw new AssertionError("Gremlins: internal error, step should not be called on values.");
      case _ => throw new DynamicTypeError(e)
    }
  }
  

  /* External Interfaces */
  
  this.debug = true // comment this out or set to false if you don't want print debugging information
  
  // Interface to run your big-step interpreter starting from an empty environment and print out
  // the test input if debugging.
  def evaluate(e: Expr): Expr = {
    require(closed(e))
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with eval ...")
      println("\nExpression:\n  " + e)
    }
    val v = eval(emp, e)
    if (debug) {
      println("Value: " + v)
    }
    v
  } 
  
  // Convenience to pass in a jsy expression as a string.
  def evaluate(s: String): Expr = evaluate(jsy.lab3.Parser.parse(s))
   
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
  def iterateStep(s: String): Expr = iterateStep(jsy.lab3.Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        jsy.lab3.Parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val v = evaluate(expr)
      println(pretty(v))
    }
    
    handle() {
      val e1 = iterateStep(expr)
      println(pretty(e1))
    }
  }
    
}
