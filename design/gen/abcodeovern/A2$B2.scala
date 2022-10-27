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
    // Self fields
    val self$: A2$B2.Interface
  
    // Self Named types
    type X
  
    // Self ADTs
    type Exp
  
    // Functions
    val eval: self$.Exp => Int
    val f: Int => Int
  
    // Cases
    def eval_cases(matched: self$.Exp): Unit => Int
  
    // Translations
    def A2$B2$$Exp(from: A2$B2.Exp): Exp
  }

  // Path implementation
  object Family extends A2$B2.Interface {
    // Self field instantiation
    override val self$: A2$B2.Interface = A2$B2.Family
  
    // Self named types instantiation
    override type X = A2$B2.X
  
    // Self ADTs instantiation
    override type Exp = A2$B2.Exp
  
    // Function implementations
    override val eval: self$.Exp => Int = eval$Impl(A2.Family, self$)
    def eval$Impl(self$1: A2.Interface, self$: A2$B2.Interface): self$.Exp => Int =
      A1$B1.Family.eval$Impl(A1.Family, self$)
    override val f: Int => Int = f$Impl(A2.Family, self$)
    def f$Impl(self$1: A2.Interface, self$: A2$B2.Interface): Int => Int =
      A1$B2.Family.f$Impl(A1.Family, self$)
  
    // Cases implementations
    def eval_cases(matched: self$.Exp): Unit => Int = eval_cases$Impl(A2.Family, self$)(matched.asInstanceOf[A2$B2.Exp])
    def eval_cases$Impl(self$1: A2.Interface, self$: A2$B2.Interface)(matched: A2$B2.Exp): Unit => Int = (ignore: Unit) => matched match {
      case matched@A2$B2.ENat2(_) =>
        val x: A2$B2.ENat2 = matched
        val x$proj = x
        (x.n + 2)
      case A2$B2.A2$B1$$Exp(inherited) =>
        A2$B1.Family.eval_cases$Impl(self$1, self$)(inherited)(ignore)
      case A2$B2.A1$B2$$Exp(inherited) =>
        A1$B2.Family.eval_cases$Impl(self$1, self$)(inherited)(ignore)
    }
  
    // Translation function implementations
    override def A2$B2$$Exp(from: A2$B2.Exp): Exp = from
    override def A2$B1$$Exp(from: A2$B1.Exp): Exp = A2$B2.A2$B1$$Exp(from)
    override def A1$B1$$Exp(from: A1$B1.Exp): Exp = A2$B2.A2$B1$$Exp(A2$B1.Family.A1$B1$$Exp(from))
    override def A1$B2$$Exp(from: A1$B2.Exp): Exp = A2$B2.A1$B2$$Exp(from)
  }
}