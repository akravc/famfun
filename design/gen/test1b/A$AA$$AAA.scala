import reflect.Selectable.reflectiveSelectable

object A$AA$$AAA {
  // Types
  

  // ADTs
  type Exp = A$AA$AAA.Exp
  ///sealed trait Exp
  // Defined constructors
  ///case class EBase() extends Exp
  // Inherited constructors
  
  

  // Path interface
  trait Interface  {
    // Self fields
    val self$1: A.Interface
    val self$: A$AA$$AAA.Interface
  
    // Self Named types
    
  
    // Self ADTs
    type Exp
  
    // Functions
    
  
    // Cases
    def eval_cases(matched: self$.Exp): Unit => Int
  
    // Translations
    ///def A$AA$$AAA$$Exp(from: A$AA$$AAA.Exp): Exp
  }

  // Path implementation
  object Family extends A$AA$$AAA.Interface {
    val delegate: A$AA$AAA.Family.type = A$AA$AAA.Family
    // Self field instantiation
    override val self$1: A.Interface = A.Family
    override val self$: A$AA$$AAA.Interface = A$AA$$AAA.Family
  
    // Self named types instantiation
    
  
    // Self ADTs instantiation
    override type Exp = delegate.self$.Exp
  
    // Function implementations
    
  
    // Cases implementations
    def eval_cases(matched: self$.Exp): Unit => Int = delegate.eval_cases(matched.asInstanceOf[delegate.self$.Exp])
    def eval_cases$Impl(self$1: A.Interface, self$: A$AA$$AAA.Interface)(matched: A$AA$$AAA.Exp): Unit => Int =
      delegate.eval_cases$Impl(self$1, delegate.self$2, delegate.self$)(matched)
  
    // Translation function implementations
    ///def A$AA$$AAA$$Exp(from: A$AA$$AAA.Exp): Exp = from
  }
}
