import reflect.Selectable.reflectiveSelectable 

object Base {
	 sealed class T; 
	 case class C1(n: Int) extends T; 
	 case class C2(n1: Int, n2: Int) extends T; 

	 val plus : (Int => (Int => Int)) = (x: Int) => (y: Int) => 1
	 val sum : (Base.T => Int) = (t: Base.T) => ( t match { 
		 case C1(n) => (r: { val arg: Base.T; }) => n; 
		 case C2(n1, n2) => (r: { val arg: Base.T; }) => Base.plus(n1)(n2); 
})( new { val arg = t; })
}
