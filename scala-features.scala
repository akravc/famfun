object trait_linearization {
trait A {
  abstract class X
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
  trait A {
    type X <: Animal
  }
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
