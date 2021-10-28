import reflect.Selectable.reflectiveSelectable

// Family Base {
//
//  type T = C1 {n: N} | C2 {n1: N, n2: N}
//
//  val plus: (N -> N -> N) = lam (x: N). lam (y: N). 1
//
//  val sum: (.T -> N) = lam (t: .T). match t with <.sum_cases> {arg = t}
//
//  cases sum_cases <.T> : {arg: .T} -> {C1: {n: N} -> N, C2: {n1: N, n2: N} -> N} =
//             lam (r: {arg: .T}). {C1 = lam (x: {n: N}). x.n, C2 = lam (x: {n1: N, n2: N}). ((.plus x.n1) x.n2)}
//
// }

object Base {
  sealed class T;
  case class C1(n: Int) extends T;
  case class C2(n1: Int, n2: Int) extends T;

  val plus : (Int => (Int => Int)) = (x: Int) => (y: Int) => 1
  val sum : (Base.T => Int) = (t: Base.T) =>
    (t match {
      case _: C1 => (x: { val n: Int; }) => (r: { val arg: Base.T; }) => x.n;
      case _: C2 => (x: { val n1: Int; val n2: Int; }) => (r: { val arg: Base.T; }) => Base.plus(x.n1)(x.n2);
    })({ val arg = t; })
}