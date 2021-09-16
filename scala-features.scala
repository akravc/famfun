object trait_linearization {
trait A { abstract class X
  case class Leaf(n: Int) extends X
  def count(x: X): Int = x match {
    case Leaf(n) => 1
  }
}

trait B extends A {
  case class Node(left: X, right: X) extends X
  override def count(x: X): Int = x match {
    case Node(left, right) => 1 + count(left) + count(right)
    case _ => super.count(x)
  }
}

trait C extends A {
  case class Container(el: X) extends X
  override def count(x: X): Int = x match {
    case Container(el) => 1 + count(el)
    case _ => super.count(x)
  }
}
object O extends A with B with C
import O._
count(Container(Node(Container(Leaf(1)),Leaf(2))))
}

object type_members {
  class Animal
  class Cat extends Animal
  class HouseCat extends Cat
  trait A { // A.X
    type X <: Animal
  }
  object a extends A // a.X
  trait B extends A {
    type X <: Cat
  }
  trait C extends B {
    type X = HouseCat
  }
  trait D {
    type X >: Cat <: Animal
  }
  trait E extends D {
    type X = Cat
  }
}

object translation_ex1 {
  val source = """
Family A {
  type X = Zero {}
  val toint: (self(A).X -> N) = lam (x: self(A).X). match x with Zero => lam (i: {}). 0
}
"""
  import TestFamParser._
  val sourceTree = parse0(famdef, source).get
}

object translation_ex2 {
  val famA = """
Family A {
  type X = Zero {}
  val toint: (self(A).X -> N) = lam (x: self(A).X). match x with Zero => lam (i: {}). 0
}
"""

  val famB = """
Family B extends A {
  type X += Succ {pred: self(A).X}
  cases toint_0: (self(A).X -> N) = Succ => lam (p: {pred: self(A).X}). 1 //1 + toint(p)
}
"""

  val mainSource = """B.toint(B.Zero{})"""

  object a extends A
  trait A {
    abstract class X
    case class Zero() extends X
    def toint(x: X): Int = x match {
      case Zero () => 0
    }
  }

  object b extends B
  trait B extends A {
    case class Succ(pred: X) extends X
    override def toint(x: X): Int = x match {
      case Succ(pred) => 1 + toint(pred)
      case _ => super.toint(x)
    }
  }

  val mainTarget = b.toint(b.Zero())
}

"""
Family A {
  Family B {
    type X = M { }

    val g : Unit -> X = lam (_ : Unit). M {}  // X means self(A.B).X
  }

  Family B2 extends B {
    type X = M { a : Int = 2 } |  N { b : X }
  }

  val h : B2.X -> B2.X =                      // B2.X means self(A).B2.X
    lam (x : B2.X). match x with C_h

  cases C_h for B2.X : B2.X =
    M => lam (r : { a : Int }). B2.M { a = r.a + 1 }
    N => lam (r : { b : B2.X }). B2.N { b = h(r.b) }
}

Family A2 extends A {
  Family B {
    type X += P { c : X }
  }

  cases C_h for B2.X : B2.X +=                // B2.X means self(A2).B2.X
    P => lam (r : { c : B2.X }). B2.P { c = h(r.c) }
}

val x0 : A2.B2.X = A2.B2.g()
val x1 : A2.B2.X = A2.B2.P { c = x0 }
val x2 : A2.B2.X = A2.B2.N { b = x1 }
h(x2)
"""
