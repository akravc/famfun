import reflect.Selectable.reflectiveSelectable

object A2$B2 {
  // Types
  type X = {val x: Boolean}

  // ADTs
  sealed trait Exp
  // Defined constructors
  case class ENat2(n: Int) extends Exp
  // Inherited constructors
  case class A2$B1$$Exp(inherited: A2$B1.Exp) extends Exp {
    override def toString(): String = inherited.toString()
  }
  case class A1$B2$$Exp(inherited: A1$B2.Exp) extends Exp {
    override def toString(): String = inherited.toString()
  }
  

  // Path interface
  trait Interface extends A2$B1.Interface with A1$B2.Interface {
    // Self Named types
    type X
  
    // Self ADTs
    type Exp
  
    // Functions
    val eval: this.Exp => Int
    val f: Int => Int
  
    // Cases
    def eval_cases(matched: this.Exp): Unit => Int
  
    // Translations
    def A2$B2$$Exp(from: A2$B2.Exp): Exp
  }

  // Path implementation
  object Family extends A2$B2.Interface {
    // Self named types instantiation
    override type X = A2$B2.X
  
    // Self ADTs instantiation
    override type Exp = A2$B2.Exp
  
    // Function implementations
    override val eval: this.Exp => Int = eval$Impl(A2.Family, this)
    def eval$Impl(self$1: A2.Interface, self$: A2$B2.Interface): self$.Exp => Int =
      A1$B1.Family.eval$Impl(self$1, self$)
    override val f: Int => Int = f$Impl(A2.Family, this)
    def f$Impl(self$1: A2.Interface, self$: A2$B2.Interface): Int => Int =
      A1$B2.Family.f$Impl(self$1, self$)
  
    // Cases implementations
    def eval_cases(matched: this.Exp): Unit => Int = eval_cases$Impl(A2.Family, this)(matched)
    def eval_cases$Impl(self$1: A2.Interface, self$: A2$B2.Interface)(matched: A2$B2.Exp): Unit => Int = (unit: Unit) => matched match {
      case matched@A2$B2.ENat2(_) =>
        val x: A2$B2.ENat2 = matched
        (x.n + 2)
      case A2$B2.A2$B1$$Exp(inherited) =>
        A2$B1.Family.eval_cases$Impl(self$1, self$)(inherited)(unit)
      case A2$B2.A1$B2$$Exp(inherited) =>
        A1$B2.Family.eval_cases$Impl(self$1, self$)(inherited)(unit)
    }
  
    // Translation function implementations
    override def A2$B2$$Exp(from: A2$B2.Exp): Exp = from
    override def A2$B1$$Exp(from: A2$B1.Exp): Exp = A2$B2.A2$B1$$Exp(from)
    override def A1$B1$$Exp(from: A1$B1.Exp): Exp = A2$B2.A2$B1$$Exp(A2$B1.Family.A1$B1$$Exp(from))
    override def A1$B2$$Exp(from: A1$B2.Exp): Exp = A2$B2.A1$B2$$Exp(from)
  }
}