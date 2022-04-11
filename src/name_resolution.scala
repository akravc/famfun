import famfun._

object name_resolution {
  // A pass that:
  // 1. resolves whether things parsed as variables are actually variables or function names and
  // 2. resolves implicit self paths.
  def resolveImplicitSelfPaths(l: Linkage): Linkage = l.copy(
    types =
      l.types.view
        .mapValues(resolveImplicitSelfPathsTypeDefn(l.self))
        .toMap
    ,
    defaults =
      l.defaults.view
        .mapValues(resolveImplicitSelfPathsDefaultDefn(l.self))
        .toMap,
    adts =
      l.adts.view
        .mapValues(resolveImplicitSelfPathsAdtDefn(l.self))
        .toMap,
    funs =
      l.funs.view
        .mapValues(resolveImplicitSelfPathsFunDefn(l.self, Set.empty))
        .toMap,
    depot =
      l.depot.view
        .mapValues(resolveImplicitSelfPathsCasesDefn(l.self, Set.empty))
        .toMap,
    nested =
      l.nested.view
        .mapValues(resolveImplicitSelfPaths)
        .toMap
  )
  def resolveImplicitSelfPathsRec(curSelf: SelfPath, boundVars: Set[String])(r: Rec): Rec = r.copy(
    fields =
      r.fields.view
        .mapValues(resolveImplicitSelfPathsExpression(curSelf, boundVars))
        .toMap
  )
  def resolveImplicitSelfPathsTypeDefn(curSelf: SelfPath)(t: TypeDefn): TypeDefn = t.copy(
    typeBody = resolveImplicitSelfPathsDefnBody { (rt: RecType) =>
      resolveImplicitSelfPathsType(curSelf)(rt).asInstanceOf[RecType]
    }(t.typeBody)
  )
  def resolveImplicitSelfPathsDefaultDefn(curSelf: SelfPath)(d: DefaultDefn): DefaultDefn = d.copy(
    defaultBody = resolveImplicitSelfPathsDefnBody { (r: Rec) =>
      resolveImplicitSelfPathsExpression(curSelf, Set.empty)(r).asInstanceOf[Rec]
    }(d.defaultBody)
  )
  def resolveImplicitSelfPathsAdtDefn(curSelf: SelfPath)(a: AdtDefn): AdtDefn = a.copy(
    adtBody = resolveImplicitSelfPathsDefnBody { (cs: Map[String, RecType]) =>
      cs.view.mapValues { (rt: RecType) =>
        resolveImplicitSelfPathsType(curSelf)(rt).asInstanceOf[RecType]
      }.toMap
    }(a.adtBody)
  )
  def resolveImplicitSelfPathsFunDefn(curSelf: SelfPath, boundVars: Set[String])(f: FunDefn): FunDefn = f.copy(
    t = resolveImplicitSelfPathsType(curSelf)(f.t).asInstanceOf[FunType],
    funBody = resolveImplicitSelfPathsDefnBody(resolveImplicitSelfPathsExpression(curSelf, boundVars))(f.funBody)
  )
  def resolveImplicitSelfPathsCasesDefn(curSelf: SelfPath, boundVars: Set[String])(c: CasesDefn): CasesDefn = c.copy(
    matchType = resolveImplicitSelfPathsType(curSelf)(c.matchType).asInstanceOf[FamType],
    t = resolveImplicitSelfPathsType(curSelf)(c.t),
    casesBody = resolveImplicitSelfPathsDefnBody(resolveImplicitSelfPathsExpression(curSelf, boundVars))(c.casesBody)
  )
  def resolveImplicitSelfPathsDefnBody[B](resolveInB: B => B)(b: DefnBody[B]): DefnBody[B] = b.copy(
    defn = b.defn.map(resolveInB)
  )
  def resolveImplicitSelfPathsExpression(curSelf: SelfPath, boundVars: Set[String])(e: Expression): Expression = e match {
    case Var(id) if !boundVars.contains(id) => FamFun(Some(Sp(curSelf)), id)
    case Lam(v, t, body) => Lam(
      v,
      resolveImplicitSelfPathsType(curSelf)(t),
      resolveImplicitSelfPathsExpression(curSelf, boundVars + v.id)(body))
    case FamFun(None, name) => FamFun(Some(Sp(curSelf)), name)
    case FamCases(None, name) => FamCases(Some(Sp(curSelf)), name)
    case App(e1, e2) => App(
      resolveImplicitSelfPathsExpression(curSelf, boundVars)(e1),
      resolveImplicitSelfPathsExpression(curSelf, boundVars)(e2)
    )
    case r@Rec(_) => resolveImplicitSelfPathsRec(curSelf, boundVars)(r)
    case Proj(e, name) => Proj(resolveImplicitSelfPathsExpression(curSelf, boundVars)(e), name)
    case Inst(t, rec) => Inst(
      resolveImplicitSelfPathsType(curSelf)(t).asInstanceOf[FamType],
      resolveImplicitSelfPathsRec(curSelf, boundVars)(rec)
    )
    case InstADT(t, cname, rec) => InstADT(
      resolveImplicitSelfPathsType(curSelf)(t).asInstanceOf[FamType],
      cname,
      resolveImplicitSelfPathsRec(curSelf, boundVars)(rec)
    )
    case Match(e, g) => Match(
      resolveImplicitSelfPathsExpression(curSelf, boundVars)(e),
      resolveImplicitSelfPathsExpression(curSelf, boundVars)(g)
    )
    case _ => e
  }
}
def resolveImplicitSelfPathsType(curSelf: SelfPath)(t: Type): Type = t match {
  case FamType(None, name) => FamType(Some(Sp(curSelf)), name)
  case FunType(input, output) => FunType(
    resolveImplicitSelfPathsType(curSelf)(input),
    resolveImplicitSelfPathsType(curSelf)(output)
  )
  case RecType(fields) => RecType(fields.view.mapValues(resolveImplicitSelfPathsType(curSelf)).toMap)
  case _ => t
}
