import reflect.Selectable.reflectiveSelectable 

object A {
	 abstract class  T{ val n: Int; }
	 abstract class  U{ val t: A.T; }
	 val wrap : (Int => A.U) = (k: Int) => (new A.U { val t = (new A.T { val n = k; }); })
	 val unwrap : (A.U => Int) = (u: A.U) => u.t.n
}
