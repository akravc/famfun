object famlang {
  case class Family(id: String)
  sealed class FamilyPath
  case class AbsoluteFamily(fam: Family) extends FamilyPath
  case class SelfFamily(fam: Family) extends FamilyPath

  sealed class Type
  case object N extends Type
  case object B extends Type
  case class Q(p: FamilyPath, id: String) extends Type
  case class F(param: Type, ret: Type) extends Type
  case class R(m: Map[String,Type]) extends Type

  def wf(t: Type): Boolean = t match {
    case N => true
    case B => true
    case F(t1,t2) => wf(t1) && wf(t2)
    case R(m) => m.filter{case (_,t) => !wf(t)}.isEmpty
  }
}