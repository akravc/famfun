import reflect.Selectable.reflectiveSelectable 

object A {
	 abstract class  T{ val n1: Int; val n2: Int; val b: Boolean; }
	 val wrap1 : (Int => A.T) = (k: Int) => (new A.T { val n2 = k; val n1 = 1; val b = true; })
	 val wrap2 : (Int => (Boolean => A.T)) = (k: Int) => (b: Boolean) => (new A.T { val n2 = k; val b = b; val n1 = 1; })
}
