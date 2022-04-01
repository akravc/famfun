import famfun._

object name_resolution {
  // A pass to resolve whether things parsed as variables are actually variables or function names.
  // Also resolves implicit self paths for functions.
  // TODO: resolve implicit self paths for everything here?
  def resolveParsedVars(l: Linkage): Linkage = l.copy(
    defaults =
      l.defaults.view
        .mapValues { case (m, r) => m -> resolveParsedVarsRec(l.self, Set.empty, r) }
        .toMap,
    funs =
      l.funs.view
        .mapValues { f => resolveParsedVarsFunDefn(l.self, Set.empty, f) }
        .toMap,
    depot =
      l.depot.view
        .mapValues { c => resolveParsedVarsCasesDefn(l.self, Set.empty, c) }
        .toMap,
    nested =
      l.nested.view
        .mapValues { nl => resolveParsedVars(nl) }
        .toMap
  )
  def resolveParsedVarsRec(curSelf: SelfPath, boundVars: Set[String], r: Rec): Rec = r.copy(
    fields =
      r.fields.view
        .mapValues(resolveParsedVarsExpression(curSelf, boundVars, _))
        .toMap
  )
  def resolveParsedVarsFunDefn(curSelf: SelfPath, boundVars: Set[String], f: FunDefn): FunDefn = f.copy(
    funBody = resolveParsedVarsDefnBody(curSelf, boundVars, f.funBody)(resolveParsedVarsExpression)
  )
  def resolveParsedVarsCasesDefn(curSelf: SelfPath, boundVars: Set[String], c: CasesDefn): CasesDefn = c.copy(
    casesBody = resolveParsedVarsDefnBody(curSelf, boundVars, c.casesBody)(resolveParsedVarsExpression)
  )
  def resolveParsedVarsDefnBody[B](curSelf: SelfPath, boundVars: Set[String], b: DefnBody[B])(resolveInB: (SelfPath, Set[String], B) => B): DefnBody[B] = {
    val DefnBody(defn, extendsFrom, furtherBindsFrom) = b
    DefnBody(
      defn.map(resolveInB(curSelf, boundVars, _)),
      extendsFrom,
      furtherBindsFrom
    )
  }
  def resolveParsedVarsExpression(curSelf: SelfPath, boundVars: Set[String], e: Expression): Expression = e match {
    case Var(id) if !boundVars.contains(id) => FamFun(Some(Sp(curSelf)), id)
    case Lam(v, t, body) => Lam(v, t, resolveParsedVarsExpression(curSelf, boundVars + v.id, body))
    case App(e1, e2) => App(
      resolveParsedVarsExpression(curSelf, boundVars, e1),
      resolveParsedVarsExpression(curSelf, boundVars, e2)
    )
    case r@Rec(_) => resolveParsedVarsRec(curSelf, boundVars, r)
    case Proj(e, name) => Proj(resolveParsedVarsExpression(curSelf, boundVars, e), name)
    case Inst(t, rec) => Inst(t, resolveParsedVarsRec(curSelf, boundVars, rec))
    case InstADT(t, cname, rec) => InstADT(t, cname, resolveParsedVarsRec(curSelf, boundVars, rec))
    case Match(e, g) => Match(
      resolveParsedVarsExpression(curSelf, boundVars, e),
      resolveParsedVarsExpression(curSelf, boundVars, g)
    )
    case _ => e
  }
}
