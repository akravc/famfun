import reflect.Selectable.reflectiveSelectable

object A2$B2 {
  // Types
  type X = {val x: Boolean}

  // ADTs
  sealed trait Exp
  // Defined constructors
  case class EPlus[self$$$Exp](e2: self$$$Exp, e1: self$$$Exp) extends Exp
  // Inherited constructors
  case class A2$B1$$Exp(inherited: A2$B1.Exp) extends Exp {
    override def toString(): String = inherited.toString()
  }
  case class A1$B2$$Exp(inherited: A1$B2.Exp) extends Exp {
    override def toString(): String = inherited.toString()
  }
  

  // Path interface
  trait Interface extends A2$B1.Interface with A1$B2.Interface { self$ =>
    // Self Named types
    type X
  
    // Self ADTs
    type Exp
  
    // Functions
    val ev: (self$.Exp => Int)
    val f: (Int => Int)
  
    // Cases
    def evc(matched: self$.Exp): (Unit => Int)
  
    // Translations
    def A2$B2$$Exp(from: A2$B2.Exp): Exp
  }

  // Path implementation
  object Family extends A2$B2.Interface { self$ =>
    // Self named types instantiation
    override type X = A2$B2.X
  
    // Self ADTs instantiation
    override type Exp = A2$B2.Exp
  
    // Function implementations
    override val ev: (self$.Exp => Int) = ev$Impl(A2.Family, self$)
    def ev$Impl(self$1: A2.Interface, self$: A2$B2.Interface): (self$.Exp => Int) =
      A1$B1.Family.ev$Impl(self$1, self$)
    override val f: (Int => Int) = f$Impl(A2.Family, self$)
    def f$Impl(self$1: A2.Interface, self$: A2$B2.Interface): (Int => Int) =
      A1$B2.Family.f$Impl(self$1, self$)
  
    // Cases implementations
    def evc(matched: self$.Exp): (Unit => Int) = evc$Impl(A2.Family, self$)(matched)
    def evc$Impl(self$1: A2.Interface, self$: A2$B2.Interface)(matched: A2$B2.Exp): (Unit => Int) = (unit: Unit) => matched match {
      case matched@A2$B2.EPlus(_, _) =>
        val x: A2$B2.EPlus[self$.Exp] = matched.asInstanceOf[A2$B2.EPlus[self$.Exp]]
        (self$.ev.asInstanceOf[(self$.Exp => Int)](x.e1) + self$.ev.asInstanceOf[(self$.Exp => Int)](x.e2))
      case A2$B2.A2$B1$$Exp(inherited) =>
        A2$B1.Family.evc$Impl(self$1, self$)(inherited)(unit)
      case A2$B2.A1$B2$$Exp(inherited) =>
        A1$B2.Family.evc$Impl(self$1, self$)(inherited)(unit)
    }
  
    // Translation function implementations
    override def A2$B2$$Exp(from: A2$B2.Exp): Exp = from
    override def A2$B1$$Exp(from: A2$B1.Exp): Exp = A2$B2.A2$B1$$Exp(from)
    override def A1$B1$$Exp(from: A1$B1.Exp): Exp = A2$B2.A2$B1$$Exp(A2$B1.Family.A1$B1$$Exp(from))
    override def A1$B2$$Exp(from: A1$B2.Exp): Exp = A2$B2.A1$B2$$Exp(from)
  }
}