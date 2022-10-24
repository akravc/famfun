import reflect.Selectable.reflectiveSelectable

object A$BB {
  // Types
  

  // ADTs
  sealed trait Exp
  // Defined constructors
  case class ENat(n: Int) extends Exp
  // Inherited constructors
  case class A$AA$$AAA$$Exp(inherited: A$AA$$AAA.Exp) extends Exp {
    override def toString(): String = inherited.toString()
  }
  

  // Path interface
  trait Interface extends A$AA$$AAA.Interface {
    // Self fields
    val self$1: A.Interface
    val self$: A$BB.Interface
  
    // Self Named types
    
  
    // Self ADTs
    type Exp
  
    // Functions
    
  
    // Cases
    def eval_cases(matched: self$.Exp): Unit => Int
  
    // Translations
    def A$BB$$Exp(from: A$BB.Exp): Exp
  }

  // Path implementation
  object Family extends A$BB.Interface {
    // Self field instantiation
    override val self$1: A.Interface = A.Family
    override val self$: A$BB.Interface = A$BB.Family
  
    // Self named types instantiation
    
  
    // Self ADTs instantiation
    override type Exp = A$BB.Exp
  
    // Function implementations
    
  
    // Cases implementations
    def eval_cases(matched: self$.Exp): Unit => Int = eval_cases$Impl(self$1, self$)(matched.asInstanceOf[A$BB.Exp])
    def eval_cases$Impl(self$1: A.Interface, self$: A$BB.Interface)(matched: A$BB.Exp): Unit => Int = (ignore: Unit) => matched match {
      case matched@A$BB.ENat(_) =>
        val x: A$BB.ENat = matched
        val x$proj = x
        x.n
      case A$BB.A$AA$$AAA$$Exp(inherited) =>
        A$AA$$AAA.Family.eval_cases$Impl(self$1, self$)(inherited)(ignore)
    }
  
    // Translation function implementations
    def A$BB$$Exp(from: A$BB.Exp): Exp = from
    ///def A$AA$AAA$$Exp(from: A$AA$AAA.Exp): Exp = A$BB.A$AA$$AAA$$Exp(from)
  }
}
