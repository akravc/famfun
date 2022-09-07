object Base {
    trait Interface {
        val wrapper: Null
        val self: Base.Interface
    }
    object Family extends Base.Interface {
        override val wrapper = null 
        override val self = Base.Family
    }

    object Base_IL {

        sealed trait Ty
        case class TUnit() extends Ty
        case class TCont(ts: List[Ty]) extends Ty

        sealed trait Val
        case class Unit() extends Val
        case class Var(x: String) extends Val

        sealed trait Exp
        case class ELet(x: String, v: Val, e: Exp) extends Exp 
        case class EApp(v: Val, vs: List[Val]) extends Exp
        case class EHalt(v: Val) extends Exp

        sealed trait Fun
        case class MkFun(n: String, xs: List[String], e: Exp) extends Fun 

        trait Interface {
            val wrapper: Base.Interface
            val self: Base_IL.Interface
            type Ty
            type Exp 
            type Val 
            type Fun
            def apply(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val]
            def apply_Cases(matched: self.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val]
        }
        object Family extends Base_IL.Interface {
            override val wrapper = Base.Family
            override val self = Base_IL.Family

            type Ty = Base_IL.Ty
            type Exp = Base_IL.Exp
            type Val = Base_IL.Val 
            type Fun = Base_IL.Fun 

            override def apply(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val] = 
                apply_Impl(wrapper, self)(fs, vs)
            def apply_Impl(wrapper: Base.Interface, self: Base_IL.Interface)(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val] =
                (v: self.Val) => { self.apply_Cases(v.asInstanceOf[self.self.Val])(fs.asInstanceOf[List[self.self.Fun]], vs.asInstanceOf[List[self.self.Val]]).asInstanceOf[Option[self.Val]] }
            override def apply_Cases(matched: self.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val] = 
                apply_Cases_Impl(wrapper, self)(matched.asInstanceOf[Base.Base_IL.Val])(fs, vs)
            def apply_Cases_Impl(wrapper: Base.Interface, self: Base_IL.Interface)(matched: Base.Base_IL.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val] =
                matched match {
                    case Unit() => None
                    case Var(x) => None
                }
        }
    }
}

object IfExt {

    trait Interface extends Base.Interface {
        val wrapper: Null
        val self: IfExt.Interface
    }
    object Family extends IfExt.Interface {
        override val wrapper = null
        override val self = IfExt.Family
    }
    
    object IfExt_IL {
        sealed trait Ty
        case class TInt() extends Ty
        case class Base_IL__Ty(inherited: Base.Base_IL.Ty) extends Ty 

        sealed trait Exp 
        case class EIf(v: Val, e1: Exp, e2: Exp) extends Exp 
        case class Base_IL__Exp(inherited: Base.Base_IL.Exp) extends Exp 

        sealed trait Val
        case class Int(i: Integer) extends Val
        case class Base_IL__Val(inherited: Base.Base_IL.Val) extends Val

        trait Interface extends Base.Base_IL.Interface {
            val wrapper: IfExt.Interface
            val self: IfExt_IL.Interface
            //def apply(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val]
            //def apply_Cases(matched: self.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val]
        }
        object Family extends IfExt_IL.Interface {
            override val wrapper = IfExt.Family
            override val self = IfExt_IL.Family
            override type Val = IfExt_IL.Val
            override type Ty = IfExt_IL.Ty 
            override type Exp = IfExt_IL.Exp
            override def apply(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val] =
                apply_Impl(wrapper, self)(fs, vs) 
            def apply_Impl(wrapper: IfExt.Interface, self: IfExt_IL.Interface)(fs: List[self.Fun], vs: List[self.Val]): self.Val => Option[self.Val] =
                Base.Base_IL.Family.apply_Impl(wrapper, self)(fs, vs)
            override def apply_Cases(matched: self.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val] =
                apply_Cases_Impl(wrapper, self)(matched.asInstanceOf[IfExt.IfExt_IL.Val])(fs, vs)
            def apply_Cases_Impl(wrapper: IfExt.Interface, self: IfExt_IL.Interface)(matched: IfExt.IfExt_IL.Val)(fs: List[self.Fun], vs: List[self.Val]): Option[self.Val] =
                matched match {
                    case Int(i) => None
                    case Base_IL__Val(inherited) => Base.Base_IL.Family.apply_Cases_Impl(wrapper, self)(inherited)(fs, vs)
                }
        }
    }
}
