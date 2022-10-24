import reflect.Selectable.reflectiveSelectable

object A$AA$AAA {
  // Types
  

  // ADTs
  sealed trait Exp
  // Defined constructors
  case class EBase() extends Exp
  // Inherited constructors
  
  

  // Path interface
  trait Interface  {
    // Self fields
    val self$1: A.Interface
    val self$2: A$AA.Interface
    val self$: A$AA$AAA.Interface
  
    // Self Named types
    
  
    // Self ADTs
    type Exp
  
    // Functions
    
  
    // Cases
    def eval_cases(matched: self$.Exp): Unit => Int
  
    // Translations
    def A$AA$AAA$$Exp(from: A$AA$AAA.Exp): Exp
  }

  // Path implementation
  object Family extends A$AA$AAA.Interface {
    // Self field instantiation
    override val self$1: A.Interface = A.Family
    override val self$2: A$AA.Interface = A$AA.Family
    override val self$: A$AA$AAA.Interface = A$AA$AAA.Family
  
    // Self named types instantiation
    
  
    // Self ADTs instantiation
    override type Exp = A$AA$AAA.Exp
  
    // Function implementations
    
  
    // Cases implementations
    def eval_cases(matched: self$.Exp): Unit => Int = eval_cases$Impl(self$1, self$2, self$)(matched.asInstanceOf[A$AA$AAA.Exp])
    def eval_cases$Impl(self$1: A.Interface, self$2: A$AA.Interface, self$: A$AA$AAA.Interface)(matched: A$AA$AAA.Exp): Unit => Int = (ignore: Unit) => matched match {
      case matched@A$AA$AAA.EBase() =>
        val ignore: A$AA$AAA.EBase = matched
        val ignore$proj = ignore
        0
    }
  
    // Translation function implementations
    def A$AA$AAA$$Exp(from: A$AA$AAA.Exp): Exp = from
  }
}