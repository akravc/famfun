import famfun.*
import MapOps.*
import PrettyPrint.*

import scala.annotation.tailrec

object name_resolution {
  def validatePath(errMsg: String, ctx: SelfPath)(path: Path): Either[String, Path] =
    if validPath(ctx)(path) then Right(path)
    else Left(errMsg)

  def validateOptPath(errMsg: String, ctx: SelfPath)(optPath: Option[Path]): Either[String, Option[Path]] = optPath match {
    case None => Right(None)
    case Some(path) => validatePath(errMsg, ctx)(path).map(Some.apply)
  }

  @tailrec
  def validPath(ctx: SelfPath)(path: Path): Boolean = path match {
    case Sp(sp) => validSelfPath(ctx)(sp)
    case AbsoluteFamily(pref, _) => validPath(ctx)(pref)
  }

  // Determines whether `selfPath` is a valid self path in the context with self path `ctx`;
  // ie: is `selfPath` a prefix of `curSelf`?
  def validSelfPath(ctx: SelfPath)(selfPath: SelfPath): Boolean = {
    @tailrec
    def isPrefix[T](lst1: List[T], lst2: List[T]): Boolean = (lst1, lst2) match {
      case (Nil, _) => true
      case (x :: xs, y :: ys) if x == y => isPrefix(xs, ys)
      case _ => false
    }

    isPrefix(selfPathToFamList(selfPath), selfPathToFamList(ctx))
  }

  // A pass that:
  // 1. resolves whether things parsed as variables are actually variables or function names and
  // 2. resolves implicit self paths.
  // 3. verifies self paths mentioned are valid.
  def resolveSelfPaths(l: Linkage): Either[String, Linkage] = for {
    resolvedSup <- l.sup match {
      case None => Right(None)
      case Some(p) =>
        validatePath(s"Invalid path ${print_path(p)} in ${print_path(l.path)}", l.self)(p).map(Some.apply)
    }
    resolvedTypes <- traverseMap(l.types)(resolveSelfPathsTypeDefn(l.self))
    resolvedDefaults <- traverseMap(l.defaults)(resolveSelfPathsDefaultDefn(l.self))
    resolvedAdts <- traverseMap(l.adts)(resolveSelfPathsAdtDefn(l.self))
    resolvedFuns <- traverseMap(l.funs)(resolveSelfPathsFunDefn(l.self, Set.empty))
    resolvedDepot <- traverseMap(l.depot)(resolveSelfPathsCasesDefn(l.self, Set.empty))
    resolvedNested <- traverseMap(l.nested)(resolveSelfPaths)
  } yield l.copy(
    sup = resolvedSup,
    types = resolvedTypes,
    defaults = resolvedDefaults,
    adts = resolvedAdts,
    funs = resolvedFuns,
    depot = resolvedDepot,
    nested = resolvedNested
  )

  def resolveSelfPathsRec(curSelf: SelfPath, boundVars: Set[String])(r: Rec): Either[String, Rec] =
    traverseMap(r.fields)(resolveSelfPathsExpression(curSelf, boundVars)).map { resolvedFields =>
      r.copy(fields = resolvedFields)
    }

  def resolveSelfPathsTypeDefn(curSelf: SelfPath)(t: TypeDefn): Either[String, TypeDefn] =
    resolveSelfPathsDefnBody { (rt: RecType) =>
      resolveSelfPathsType(curSelf)(rt).asInstanceOf[Either[String, RecType]]
    }(t.typeBody).map { resolvedTypeBody =>
      t.copy(typeBody = resolvedTypeBody)
    }

  def resolveSelfPathsDefaultDefn(curSelf: SelfPath)(d: DefaultDefn): Either[String, DefaultDefn] =
    resolveSelfPathsDefnBody { (r: Rec) =>
      resolveSelfPathsExpression(curSelf, Set.empty)(r).asInstanceOf[Either[String, Rec]]
    }(d.defaultBody).map { resolvedDefaultBody =>
      d.copy(defaultBody = resolvedDefaultBody)
    }

  def resolveSelfPathsAdtDefn(curSelf: SelfPath)(a: AdtDefn): Either[String, AdtDefn] =
    resolveSelfPathsDefnBody { (cs: Map[String, RecType]) =>
      traverseMap(cs) { (rt: RecType) =>
        resolveSelfPathsType(curSelf)(rt).asInstanceOf[Either[String, RecType]]
      }
    }(a.adtBody).map { resolvedAdtBody =>
      a.copy(adtBody = resolvedAdtBody)
    }

  def resolveSelfPathsFunDefn(curSelf: SelfPath, boundVars: Set[String])(f: FunDefn): Either[String, FunDefn] = for {
    resolvedT <- resolveSelfPathsType(curSelf)(f.t).asInstanceOf[Either[String, FunType]]
    resolvedFunBody <- resolveSelfPathsDefnBody(resolveSelfPathsExpression(curSelf, boundVars))(f.funBody)
  } yield f.copy(t = resolvedT, funBody = resolvedFunBody)

  def resolveSelfPathsCasesDefn(curSelf: SelfPath, boundVars: Set[String])(c: CasesDefn): Either[String, CasesDefn] = for {
    resolvedMatchType <- resolveSelfPathsType(curSelf)(c.matchType).asInstanceOf[Either[String, FamType]]
    resolvedT <- resolveSelfPathsType(curSelf)(c.t)
    resolvedCasesBody <- resolveSelfPathsDefnBody(resolveSelfPathsExpression(curSelf, boundVars))(c.casesBody)
  } yield c.copy(matchType = resolvedMatchType, t = resolvedT, casesBody = resolvedCasesBody)

  def resolveSelfPathsDefnBody[B](resolveInB: B => Either[String, B])(b: DefnBody[B]): Either[String, DefnBody[B]] = b.defn match {
    case None => Right(b)
    case Some(defn) => resolveInB(defn).map { resolvedDefn => b.copy(defn = Some(resolvedDefn)) }
  }

  def resolveSelfPathsExpression(curSelf: SelfPath, boundVars: Set[String])(e: Expression): Either[String, Expression] = e match {
    case Var(id) if !boundVars.contains(id) => Right(FamFun(Some(Sp(curSelf)), id))
    case Lam(v, t, body) => for {
      resolvedT <- resolveSelfPathsType(curSelf)(t)
      resolvedBody <- resolveSelfPathsExpression(curSelf, boundVars + v.id)(body)
    } yield Lam(v, resolvedT, resolvedBody)
    case FamFun(None, name) => Right(FamFun(Some(Sp(curSelf)), name))
    case FamFun(Some(p), name) =>
      validatePath(s"Invalid path ${print_path(p)} in ${print_path(concretizePath(Sp(curSelf)))}", curSelf)(p).map { validatedP =>
        FamFun(Some(validatedP), name)
      }
    case FamCases(None, name) => Right(FamCases(Some(Sp(curSelf)), name))
    case FamCases(Some(p), name) =>
      validatePath(s"Invalid path ${print_path(p)} in ${print_path(concretizePath(Sp(curSelf)))}", curSelf)(p).map { validatedP =>
        FamFun(Some(validatedP), name)
      }
    case App(e1, e2) => for {
      resolvedE1 <- resolveSelfPathsExpression(curSelf, boundVars)(e1)
      resolvedE2 <- resolveSelfPathsExpression(curSelf, boundVars)(e2)
    } yield App(resolvedE1, resolvedE2)
    case r@Rec(_) => resolveSelfPathsRec(curSelf, boundVars)(r)
    case Proj(e, name) => resolveSelfPathsExpression(curSelf, boundVars)(e).map { resolvedE =>
      Proj(resolvedE, name)
    }
    case Inst(t, rec) => for {
      resolvedT <- resolveSelfPathsType(curSelf)(t).asInstanceOf[Either[String, FamType]]
      resolvedRec <- resolveSelfPathsRec(curSelf, boundVars)(rec)
    } yield Inst(resolvedT, resolvedRec)
    case InstADT(t, cname, rec) => for {
      resolvedT <- resolveSelfPathsType(curSelf)(t).asInstanceOf[Either[String, FamType]]
      resolvedRec <- resolveSelfPathsRec(curSelf, boundVars)(rec)
    } yield InstADT(resolvedT, cname, resolvedRec)
    case Match(e, g) => for {
      resolvedE <- resolveSelfPathsExpression(curSelf, boundVars)(e)
      resolvedG <- resolveSelfPathsExpression(curSelf, boundVars)(g)
    } yield Match(resolvedE, resolvedG)
    case ABinExp(a1, op, a2) => for {
      resolvedA1 <- resolveSelfPathsExpression(curSelf, boundVars)(a1)
      resolvedA2 <- resolveSelfPathsExpression(curSelf, boundVars)(a2)
    } yield ABinExp(resolvedA1, op, resolvedA2)
    case BBinExp(e1, op, e2) => for {
      resolvedE1 <- resolveSelfPathsExpression(curSelf, boundVars)(e1)
      resolvedE2 <- resolveSelfPathsExpression(curSelf, boundVars)(e2)
    } yield BBinExp(resolvedE1, op, resolvedE2)
    case BNot(e) => resolveSelfPathsExpression(curSelf, boundVars)(e).map(BNot.apply)
    case StringInterpolated(interpolated) =>
      val resolveAttemptedInterpolated = interpolated.map {
        case InterpolatedComponent(exp) => resolveSelfPathsExpression(curSelf, boundVars)(exp).map(InterpolatedComponent.apply)
        case comp => Right(comp)
      }
      if resolveAttemptedInterpolated.forall(_.isRight)
      then Right(StringInterpolated(resolveAttemptedInterpolated.map(_.getOrElse(throw new Exception("...")))))
      else Left("TODO invalid string interpolation")
    case IfThenElse(condExpr, ifExpr, elseExpr) => for {
      resolvedCondExpr <- resolveSelfPathsExpression(curSelf, boundVars)(condExpr)
      resolvedIfExpr <- resolveSelfPathsExpression(curSelf, boundVars)(ifExpr)
      resolvedElseExpr <- resolveSelfPathsExpression(curSelf, boundVars)(elseExpr)
    } yield IfThenElse(resolvedCondExpr, resolvedIfExpr, resolvedElseExpr)
    case _ => Right(e)
  }

  def resolveSelfPathsType(curSelf: SelfPath)(t: Type): Either[String, Type] = t match {
    case FamType(None, name) => Right(FamType(Some(Sp(curSelf)), name))
    case FamType(Some(p), name) =>
      validatePath(s"Invalid path ${print_path(p)} in ${print_path(concretizePath(Sp(curSelf)))}", curSelf)(p).map { validatedP =>
        FamType(Some(validatedP), name)
      }
    case FunType(input, output) => for {
      resolvedInput <- resolveSelfPathsType(curSelf)(input)
      resolvedOutput <- resolveSelfPathsType(curSelf)(output)
    } yield FunType(resolvedInput, resolvedOutput)
    case RecType(fields) => traverseMap(fields)(resolveSelfPathsType(curSelf)).map(RecType.apply)
    case _ => Right(t)
  }
}