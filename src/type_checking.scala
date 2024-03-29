import rep.*
import PrettyPrint.*
import MapOps.*
import ListOps.eitherFromList
import OptionOps.lastSome

import scala.annotation.tailrec

object type_checking {
  val cache: scala.collection.mutable.Map[Path, Linkage] = scala.collection.mutable.Map.empty

  def init(progLkg: Linkage): Unit = {
    cache.clear()
    cache += Sp(Prog) -> progLkg
  }

  def resolvedImplicitPathFor[A](getDefns: Linkage => Map[String, A])(curLkg: Linkage, name: String): Either[String, Path] = curLkg.path match {
    case Sp(Prog) => Left(s"Unable to resolve implicit path for $name")
    case Sp(sp) => throw new Exception("path of Linkage should never be a self path")
    case AbsoluteFamily(pref, _) =>
      getDefns(curLkg).get(name) match {
        case None =>
          getCompleteLinkage(pref).flatMap(nextLkg => resolvedImplicitPathFor(getDefns)(nextLkg, name)).orElse(curLkg.sup match {
            case None => Left(s"Unable to resolve implicit path for $name")
            case Some(supPath) => getCompleteLinkage(supPath).flatMap(nextLkg => resolvedImplicitPathFor(getDefns)(nextLkg, name).map(subSelfInPath(curLkg.self,nextLkg.self)))
          })
        case Some(_) => Right(Sp(curLkg.self))
      }
  }
  def resolveImplicitPathForType(curLkg: Linkage, typeName: String): Either[String, Path] =
    resolvedImplicitPathFor(_.types)(curLkg, typeName)
  def resolveImplicitPathForAdt(curLkg: Linkage, adtName: String): Either[String, Path] =
    resolvedImplicitPathFor(_.adts)(curLkg, adtName)
  def resolveImplicitPathForFun(curLkg: Linkage, funName: String): Either[String, Path] =
    resolvedImplicitPathFor(_.funs)(curLkg, funName)
  def resolveImplicitPathForCases(curLkg: Linkage, casesName: String): Either[String, Path] =
    resolvedImplicitPathFor(_.depot)(curLkg, casesName)

  sealed trait InheritForm
  case object Extends extends InheritForm
  case object FurtherBinds extends InheritForm
  // Marks definitions in the top-level of l as extended or further bound.
  // Recursively marks nested definitions as further bound(???)
  def markInheritForm(form: InheritForm)(l: Linkage): Linkage = {
    // Sets `extendsFrom` or `furtherBindsFrom` to the self(?) path of `l` based on `form`
    // and makes `defn` `None` as either:
    //   1. a new definition will extend it
    //   2. it will be inherited only.
    // This, along with when things are extended and further bound, are handled by the concatenation functions.
    def markBody[B](body: DefnBody[B]): DefnBody[B] = form match {
      case Extends => body.copy(defn = None, extendsFrom = Some(l.path))
      case FurtherBinds => body.copy(defn = None, furtherBindsFrom = Some(l.path))
    }
    l.copy(
      types = l.types.view.mapValues { typeDefn =>
        typeDefn.copy(typeBody = markBody(typeDefn.typeBody))
      }.toMap,
      defaults= l.defaults.view.mapValues { defaultDefn =>
        defaultDefn.copy(defaultBody = markBody(defaultDefn.defaultBody))
      }.toMap,
      adts = l.adts.view.mapValues { adtDefn =>
        adtDefn.copy(adtBody = markBody(adtDefn.adtBody))
      }.toMap,
      funs = l.funs.view.mapValues { funDefn =>
        funDefn.copy(funBody = markBody(funDefn.funBody))
      }.toMap,
      depot = l.depot.view.mapValues { casesDefn =>
        casesDefn.copy(casesBody = markBody(casesDefn.casesBody))
      }.toMap,
      nested = l.nested.view.mapValues { nestedLkg =>
        markInheritForm(FurtherBinds)(nestedLkg)
      }.toMap
    )
  }
  def collectAllConstructors(adtDefn: AdtDefn): Either[String, Map[String, RecType]] =
    Right(adtDefn.adtBody.allDefns.flatten.toMap)

  def collectAllNamedTypeFields(typeDefn: TypeDefn): Either[String, Map[String, Type]] =
    Right(typeDefn.typeBody.allDefns.map(_.fields).flatten.toMap)

  def collectAllDefaults(defaultDefn: DefaultDefn): Either[String, Map[String, Expression]] =
    Right(defaultDefn.defaultBody.allDefns.map(_.fields).flatten.toMap)

  def collectAllCaseHandlerTypes(casesDefn: CasesDefn): Either[String, Map[String, Type]] = {
    Right(casesDefn.ts.map { t => t match {
      case RecType (cfTypes) => cfTypes
      case FunType (RecType (_), RecType (cfTypes)) => cfTypes
      case _ => throw new Exception(s"Invalid shape for cases type: ${print_type(t)}")
    }}.flatten.toMap)
  }

  def unifyTypes(types: List[Type]): Either[String, Type] = types match {
    case Nil => Left("No types given to unify")
    case t :: ts => ts.foldLeft(Right(t).withLeft[String]) { (eAccType, curType) =>
      for {
        accType <- eAccType
        // TODO: needs to handle RecTypes specially instead; find common fields between all RecTypes...
        isSubFwd <- isSubtype(accType, curType)
        isSubBwd <- isSubtype(curType, accType)
        result <-
          if isSubFwd then Right(curType)
          else if isSubBwd then Right(accType)
          else Left(s"Failed to unify types: ${types.map(print_type).mkString(", ")}")
      } yield result
    }
  }

  // If the given `path` is absolute, produces the concrete version of the given type `t`
  def interpretType(path: Path, t: Type): Type = path match {
    case AbsoluteFamily(_, _) => concretizeType(t)
    case _ => t
  }

  def wf(t: Type): Either[String, Boolean] = t match {
    // _________________ WF_Num
    // K |-  WF(N)
    case NType => Right(true)

    // _________________ WF_Bool
    // K |-  WF(B)
    case BType => Right(true)

    // ----------------- WF_String
    // K |- WF(String)
    case StringType => Right(true)

    // K |- a ~> L
    // R in L.TYPES \/ R in L.ADTS
    // ____________________________ WF_Member
    // K |- WF(a.R)
    case FamType(Some(path), name) =>
      getCompleteLinkage(path).map { lkg =>
        lkg.types.contains(name) || lkg.adts.contains(name)
      }

    // K |- WF(T)
    // K |- WF(T')
    // ____________________ WF_Arrow
    // K |- WF(T -> T')
    case FunType(t1, t2) => for {
      wft1 <- wf(t1)
      wft2 <- wf(t2)
    } yield wft1 && wft2

    // forall i, K |- WF(T_i)
    // forall i j, i != j --> f_i != f_j
    // ___________________________________WF_RecordType
    // K |- WF({(f_i: T_i)*})
    case RecType(m) => m.values.foldLeft(Right(true).withLeft[String]) { (getAcc, cur) =>
      for { acc <- getAcc; wfcur <- wf(cur) } yield acc && wfcur
    }

    case _ => Right(false)
  }

  def isSubtype(t1: Type, t2: Type): Either[String, Boolean] = {
    // _____________ Sub-Refl
    // K |- T <: T
    if t1 == t2 then Right(true)
    else (t1, t2) match {
      // K |- a ~> L
      // R = T in L.TYPES
      // K |- T <: T'
      // __________________ Sub-Fam
      // K |- a.R <: T'
      case (FamType(Some(a), r), tPrime) => for {
        aLkg <- getCompleteLinkage(a)
        result <- aLkg.types.get(r) match {
          case None =>
            aLkg.adts.get(r) match {
              case None => Left(s"No such type ${print_type(t1)}")
              case Some(_) => Right(false)
            }
          case Some(tTypeDefn) => for {
            fields <- collectAllNamedTypeFields(tTypeDefn)
            t = RecType(fields)
            result <- isSubtype(t, tPrime)
          } yield result
        }
      } yield result

      // K |- T1 <: S1
      // K |- S2 <: T2
      // _________________________ Sub-Fun
      // K |- S1 -> S2 <: T1 -> T2
      case (FunType(s1, s2), FunType(t1, t2)) => for {
        sub1 <- isSubtype(t1, s1)
        sub2 <- isSubtype(s2, t2)
      } yield sub1 && sub2

      // forall j,
      //     (exists T',
      //         K |- T' <: T_j /\ (f_j: T') in {(f_i: T_i)*})
      // _______________________________________________________ Sub-Rec
      // K |- {(f_i: T_i)*} <: {(f_j: T_j)*}
      case (RecType(fis), RecType(fjs)) => Right(fjs.forall { (fj, tj) =>
        fis.get(fj) match {
          case None => false
          case Some(ti) => isSubtype(ti, tj).getOrElse(false)
        }
      })

      case _ => Right(false)
    }
  }

  def typeCheckLinkage(l: Linkage): Either[String, Unit] = for {
    completeL <- getCompleteLinkage(Sp(l.self))
    _ <- traverseMap(completeL.defaults) { d =>
      val assocType = completeL.types.getOrElse(d.name, throw new Exception("Should not happen by construction"))
      typeCheckDefaultDefns(completeL, assocType)(d)
    }
    _ <- traverseMap(completeL.funs)(typeCheckFunDefns(completeL))
    _ <- traverseMap(completeL.depot)(typeCheckCasesDefns(completeL))
    _ <- traverseMap(completeL.nested)(typeCheckLinkage)
  } yield ()

  def typeCheckDefaultDefns(curLkg: Linkage, assocType: TypeDefn)(d: DefaultDefn): Either[String, Unit] = (assocType.typeBody, d.defaultBody) match {
    case (DefnBody(None, _, _, _), DefnBody(None, _, _, _)) => Right(())
    case (DefnBody(Some(fieldTypes), _, _, _), DefnBody(Some(defn), _, _, _)) =>
      traverseWithKeyMap(defn.fields) { (fieldName, expr) =>
        for {
          eType <- typeOfExpression(curLkg, Map.empty)(expr)
          fieldType = fieldTypes.fields.getOrElse(fieldName, throw new Exception("Should not happen by construction"))
          isSub <- isSubtype(eType, fieldType)
          result <-
            if isSub then Right(())
            else Left(
              s"""Type mismatch for default value ${print_exp(expr)} for field $fieldName in type ${assocType.name} in ${print_path(curLkg.path)}:
                 |Found:    ${print_type(eType)}
                 |Required: ${print_type(fieldType)}
                 |""".stripMargin
            )
        } yield result
      }.map(_ => ())
    case _ => throw new Exception("Should not happen by construction")
  }

  def typeCheckFunDefns(curLkg: Linkage)(f: FunDefn): Either[String, Unit] = f.funBody match {
    case DefnBody(None, _, _, _) => Right(())
    case DefnBody(Some(defn), _, _, _) => for {
      defnType <- typeOfExpression(curLkg, Map.empty)(defn)
      isSub <- isSubtype(defnType, f.t)
      result <-
        if isSub then Right(())
        else Left(
          s"""Type mismatch error for function `${f.name}` in ${print_path(curLkg.path)}:
             |Found:    ${print_type(defnType)}
             |Required: ${print_type(f.t)}
             |""".stripMargin
        )
    } yield result
  }

  def typeCheckCasesDefns(curLkg: Linkage)(c: CasesDefn): Either[String, Unit] = {
    for {
      allCaseHandlerTypes <- collectAllCaseHandlerTypes(c)
      caseHandlerTypesAsCtors <- traverseMap(allCaseHandlerTypes) {
        case FunType(RecType(fields), _) => Right(RecType(fields))
        case t => Left(s"Invalid case handler type: ${print_type(t)}")
      }
      matchTypePath = c.matchType.path.getOrElse(throw new Exception("Should not have None path at this point"))
      matchTypeLkg <- getCompleteLinkage(matchTypePath)
      matchAdtDefn <-
        matchTypeLkg.adts
          .get(c.matchType.name)
          .fold(Left(s"No ADT ${c.matchType.name} in ${print_path(c.matchType.path.get)}"))(Right.apply)

      allCtors: Map[String, RecType] <- collectAllConstructors(matchAdtDefn)

      // Exhaustive check
      _ <-
      if caseHandlerTypesAsCtors == allCtors
      then Right(())
      else Left(
        s"""Cases ${c.name} in ${print_path(curLkg.path)} is non-exhaustive.
           |Found:    ${caseHandlerTypesAsCtors.mapValues(print_type).mkString(", ")}
           |Required: ${allCtors.mapValues(print_type).mkString(", ")}
           |""".stripMargin)
      caseHandlerOutTypes <- traverseMap(allCaseHandlerTypes) {
        case FunType(_, outType) => Right(outType)
        case t => Left(s"Invalid type ${print_type(t)} for case handler for cases ${c.name} in ${print_path(curLkg.path)}")
      }.map(_.values.toList)
      // Consistent result type check
      _ <- unifyTypes(caseHandlerOutTypes).left.map { unifyErrMsg =>
        s"""Inconsistent output types for case handlers for cases ${c.name} in ${print_path(curLkg.path)}:
            |$unifyErrMsg
            |""".stripMargin
      }

      // Check body
      _ <- c.casesBody.defn match {
        case None => Right(())
        case Some(defn) => for {
          defnType <- typeOfExpression(curLkg, Map.empty)(defn)
          isSub <- isSubtype(defnType, c.t)
          result <-
            if isSub then Right(())
            else Left(
              s"""Type mismatch error for cases `${c.name}` in ${print_path(curLkg.path)}:
                 |Found:    ${print_type(defnType)}
                 |Required: ${print_type(c.t)}
                 |""".stripMargin
            )
        } yield result
      }
    } yield ()
  }

  def resolveImplicitPathsInType(curLkg: Linkage)(t: Type): Either[String, Type] = t match {
    case toResolve@FamType(None, name) => for {
      resolvedPath <- resolveImplicitPathForType(curLkg, name).orElse(resolveImplicitPathForAdt(curLkg, name))
    } yield { toResolve.path = Some(resolvedPath); t }
    case FunType(input, output) => for {
      _ <- resolveImplicitPathsInType(curLkg)(input)
      _ <- resolveImplicitPathsInType(curLkg)(output)
    } yield t
    case RecType(fields) => for {
      _ <- traverseMap(fields)(resolveImplicitPathsInType(curLkg))
    } yield t
    case _ => Right(t)
  }
  def resolveImplicitPathsInExprShallow(curLkg: Linkage)(e: Expression): Either[String, Expression] = e match {
    case Lam(_, toResolve, _) => for {
      _ <- resolveImplicitPathsInType(curLkg)(toResolve)
    } yield e
    case toResolve@FamFun(None, funName) => for {
      resolvedPath <- resolveImplicitPathForFun(curLkg, funName)
    } yield { toResolve.path = Some(resolvedPath); e }
    case toResolve@FamCases(None, casesName) => for {
      resolvedPath <- resolveImplicitPathForCases(curLkg, casesName)
    } yield { toResolve.path = Some(resolvedPath); e }
    case Inst(toResolve@FamType(None, typeName), _) => for {
      resolvedPath <- resolveImplicitPathForType(curLkg, typeName)
    } yield { toResolve.path = Some(resolvedPath); e }
    case InstADT(toResolve@FamType(None, adtName), _, _) => for {
      resolvedPath <- resolveImplicitPathForAdt(curLkg, adtName)
    } yield { toResolve.path = Some(resolvedPath); e }
    case Match(_, App(toResolve@FamCases(None, casesName), Rec(_))) => for {
      resolvedPath <- resolveImplicitPathForCases(curLkg, casesName)
    } yield { toResolve.path = Some(resolvedPath); e }
    case _ => Right(e)
  }
  def typeOfExpression(curLkg: Linkage, G: Map[String, Type])(e: Expression): Either[String, Type] =
    resolveImplicitPathsInExprShallow(curLkg)(e).flatMap { _ =>
      e match {
        // _________________ T_Num
        // K, G |- n : N
        case NConst(_) => Right(NType)

        // K, G |- a1 : N
        // K, G |- a2 : N
        // `op` \in {+, -, *, /}
        // ------------------ T_AOp
        // K, G |- a1 `op` a2 : N
        case ABinExp(a1, _, a2) => for {
          a1Type <- typeOfExpression(curLkg, G)(a1)
          a2Type <- typeOfExpression(curLkg, G)(a2)
          result <- (a1Type, a2Type) match {
            case (NType, NType) => Right(NType)
            case (NType, _) => Left(
              s"""Type mismatch for ${print_exp(a2)}, the right-hand side of ${print_exp(e)}.
                 |Found:    ${print_type(a2Type)}
                 |Required: N
                 |""".stripMargin
            )
            case _ => Left(
              s"""Type mismatch for ${print_exp(a1)}, the left-hand side of ${print_exp(e)}.
                 |Found:    ${print_type(a1Type)}
                 |Required: N
                 |""".stripMargin
            )
          }
        } yield result

        // _________________ T_Bool
        // K, G |- b : B
        case BConst(_) => Right(BType)

        case BBinExp(e1, op, e2) => for {
          e1Type <- typeOfExpression(curLkg, G)(e1)
          e2Type <- typeOfExpression(curLkg, G)(e2)
          result <- op match {
            case BAnd | BOr => (e1Type, e2Type) match {
              case (BType, BType) => Right(BType)
              case (BType, _) => Left(
                s"""Type mismatch for ${print_exp(e2)}, the right-hand side of ${print_exp(e)}.
                   |Found:    ${print_type(e2Type)}
                   |Required: B
                   |""".stripMargin
              )
              case _ => Left(
                s"""Type mismatch for ${print_exp(e1)}, the left-hand side of ${print_exp(e)}.
                   |Found:    ${print_type(e1Type)}
                   |Required: B
                   |""".stripMargin
              )
            }

            case BEq | BNeq => for {
              isSubFwd <- isSubtype(e1Type, e2Type)
              isSubBwd <- isSubtype(e2Type, e1Type)
              result <-
                if isSubFwd || isSubBwd
                then Right(BType)
                else Left(
                  s"""Type mismatch for ${print_exp(e2)}, the right-hand side of ${print_exp(e)}.
                     |Found:    ${print_type(e2Type)}
                     |Required: ${print_type(e1Type)}
                     |""".stripMargin
                )
            } yield result

            case BLt | BGt | BLeq | BGeq => (e1Type, e2Type) match {
              case (NType, NType) => Right(BType)
              case (NType, _) => Left(
                s"""Type mismatch for ${print_exp(e2)}, the right-hand side of ${print_exp(e)}.
                   |Found:    ${print_type(e2Type)}
                   |Required: N
                   |""".stripMargin
              )
              case _ => Left(
                s"""Type mismatch for ${print_exp(e1)}, the left-hand side of ${print_exp(e)}.
                   |Found:    ${print_type(e1Type)}
                   |Required: N
                   |""".stripMargin
              )
            }
          }
        } yield result

        case BNot(inner) => typeOfExpression(curLkg, G)(inner).flatMap {
          case BType => Right(BType)
          case innerType => Left(
            s"""Type mismatch for ${print_exp(inner)}, the inner expression of ${print_exp(e)}.
               |Found:    ${print_type(innerType)}
               |Required: B
               |""".stripMargin
          )
        }

        // K, G |- e0 : B
        // K, G |- e1 : T
        // K, G |- e2 : T
        // ---------------------------------- T_IfThenElse
        // K, G |- if e0 then e1 else e2 : T
        case IfThenElse(condExpr, ifExpr, elseExpr) => for {
          condType <- typeOfExpression(curLkg, G)(condExpr)
          ifType <- typeOfExpression(curLkg, G)(ifExpr)
          elseType <- typeOfExpression(curLkg, G)(elseExpr)
          result <- condType match {
            case BType => unifyTypes(List(ifType, elseType))
            case _ => Left(
              s"""Type mismatch for ${print_exp(condExpr)}, the condition of if expression ${print_exp(e)}.
                 |Found:    ${print_type(condType)}
                 |Required: B
                 |""".stripMargin
            )
          }
        } yield result

        case StringLiteral(_) => Right(StringType)
        case StringInterpolated(interpolated) =>
          if interpolated.forall {
            case StringComponent(_) => true
            case InterpolatedComponent(exp) => typeOfExpression(curLkg, G)(exp).isRight
          } then Right(StringType) else Left("TODO invalid interpolated string")

        // x: T \in G
        // ________________T_Var
        // K, G |- x : T
        case Var(x) => G.get(x).fold(Left(s"Variable $x unbound"))(Right.apply)

        // K |- WF(T)
        // K, (x : T, G) |- body : T'
        // _____________________________________ T_Lam
        // K, G |- lam (x : T). body : T -> T'
        case Lam(Var(x), xType, body) => for {
          xTypeWF <- wf(xType)
          result <-
            if xTypeWF then typeOfExpression(curLkg, G + (x -> xType))(body).map(FunType(xType, _))
            else Left(s"Type $xType is not well-formed")
        } yield result

        // K, G |- e : T
        // K, G |- g : T -> T'
        // _____________________ T_App
        // K, G |- g e : T'
        case App(e1, e2) =>
          typeOfExpression(curLkg, G)(e1).flatMap { // type e1
            case FunType(iType, oType) => for {
              e2Type <- typeOfExpression(curLkg, G)(e2)
              isSub <- isSubtype(e2Type, iType)
              result <-
                if isSub then Right(oType)
                else {
                  val e1Pretty = print_exp(e1)
                  val e2Pretty = print_exp(e2)
                  Left(
                    s"""Cannot apply $e2Pretty to $e1Pretty;
                       |$e1Pretty expects an argument of type ${print_type(iType)} but got one of type ${print_type(e2Type)}.
                       |""".stripMargin
                  )
                }
            } yield result
            case _ =>
              val e1Pretty = print_exp(e1)
              val e2Pretty = print_exp(e2)
              Left(
                s"""Cannot apply $e1Pretty to $e2Pretty;
                   |$e1Pretty does not have a function type.
                   |""".stripMargin
              )
          }

        // forall i,
        //     K, G |- e_i : T_i
        // ________________________________________ T_Rec
        // K, G |- {(f_i = e_i)*} : {(f_i: T_i)*}
        case Rec(fields) =>
          traverseMap(fields)(typeOfExpression(curLkg, G)).map(RecType.apply)

        // K, G |- e : {(f': T')*}
        // (f: T) in (f': T')*
        // _________________________ T_Proj
        // K, G |- e.f : T
        case Proj(e, f) =>
          typeOfExpression(curLkg, G)(e).flatMap {
            case RecType(fTypes) =>
              fTypes.get(f).fold(Left("TODO no such field"))(Right.apply)
            // if we have an instance of a type, the inferred type will be a famtype
            case FamType(Some(p), typeName) => for {
              lkg <- getCompleteLinkage(p)
              typeDefn <- lkg.types.get(typeName).fold(Left("TODO no such named type"))(Right.apply)
              allTypeFields: Map[String, Type] <- collectAllNamedTypeFields(typeDefn)
              result <- allTypeFields.get(f).fold(Left("TODO no such field"))(Right.apply)
            } yield result

            case _ => Left("TODO invalid projection")
          }

        // K |- a ~> L
        // m : (T -> T') = lam (x : T). body in L.FUNS
        // _______________________________________________ T_FamFun
        // K, G |- a.m : T -> T'
        case FamFun(Some(path), name) => for {
          lkg <- getCompleteLinkage(path)
          funDefn <- lkg.funs.get(name).fold(Left(s"No such function $name"))(Right.apply)
          fType = funDefn.t
        } yield interpretType(path, fType)

        // K |- a ~> L
        // r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*} =
        //         lam (x: {(f_i:T_i)*}). body in L.CASES
        // _______________________________________________________________ T_Cases
        // K, G |- a.r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*}
        case FamCases(Some(path), name) => for {
          lkg <- getCompleteLinkage(path)
          // Validity of type for the defined `cases` will be checked at the top level (ie, match type works with defnType)
          casesDefn <- lkg.depot.get(name).fold(Left("TODO no such cases"))(Right.apply)
          casesType = casesDefn.t
        } yield interpretType(path, casesType)

        // K |- a ~> L
        // R = {(f_i: T_i)*} in L.TYPES
        // forall i,
        //     K, G |- e_i : T_i
        // ______________________________________ T_Constructor
        // K, G |- a.R({(f_i = e_i)*}) : a.R
        case Inst(famType@FamType(Some(path), typeName), rec) => for {
          lkg <- getCompleteLinkage(path)
          typeDefn <- lkg.types.get(typeName).fold(Left(s"No type $typeName in $path"))(Right.apply)
          allTypeFields: Map[String, Type] <- collectAllNamedTypeFields(typeDefn)
          _ <- traverseWithKeyMap(rec.fields) { (f: String, e: Expression) => for {
            // typeCheck all fields wrt linkage definition
            fieldType <- allTypeFields.get(f).fold(Left("TODO no such field"))(Right.apply)
            eType <- typeOfExpression(curLkg, G)(e)
            isSub <-isSubtype(eType, fieldType)
            result <- if isSub then Right(()) else Left("TODO field types in instance don't match")
          } yield result }
          defaults <- lkg.defaults.get(typeName).fold(Right(Map.empty))(collectAllDefaults)
          _ <- traverseWithKeyMap(allTypeFields) { (f: String, t: Type) =>
            if (rec.fields.contains(f) || defaults.contains(f)) Right(()) else Left(s"Expected field $f")
          }
        } yield famType

        //  R = \overline{C' {(f': T')*}} in {{a}}
        //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
        //  forall i, G |- e_i : T_i
        //_________________________________________________ T_ADT
        //  G |- a.R(C {(f_i = e_i)*}) : a.R
        case InstADT(famType@FamType(Some(path), tName), cname, rec) =>
          for {
            instFields <- traverseMap(rec.fields)(typeOfExpression(curLkg, G))
            lkg <- getCompleteLinkage(path)
            adtDefn <- lkg.adts.get(tName).fold(Left(s"No ADT $tName in ${print_path(path)}")) (Right.apply)
            allCtors <- collectAllConstructors(adtDefn)
            ctorRecType <- allCtors.get(cname).fold(Left(s"No constructor $cname for $tName in ${print_path(path)}"))(Right.apply)
            ctorFields = ctorRecType.fields

            instFieldsType = RecType(instFields)
            ctorFieldsType0 = RecType(ctorFields)
            ctorFieldsType = path match {
              case AbsoluteFamily(_, _) => concretizeType(ctorFieldsType0)
              case _ => ctorFieldsType0
            }
            // we do not allow subtyping within ADT records right now
            result <-
              if instFieldsType == ctorFieldsType then Right(famType)
              else Left(
                s"""Mismatching field types in ADT instance for $tName with constructor $cname in ${print_path(path)}:
                   |Instance field types: ${print_type(instFieldsType)}
                   |Required field types: ${print_type(ctorFieldsType)}
                   |""".stripMargin
              )
          } yield result

        // K |- a ~> L
        // K, G |- e : a.R
        // R = \overline{C_i {(f_i: T_i)*}} in L.ADTS
        // g = a'.r {(f_arg = e_arg)*}
        // K, G |- g: {(C_i: {(f_i: T_i)*} -> T')*}
        // ___________________________________________ T_Match
        // K, G |- match e with g : T'
        case Match(e, g) =>
          typeOfExpression(curLkg, G)(e).flatMap {
            case FamType(Some(path), tName) => for {
              lkg <- getCompleteLinkage(path)
              adtDefn <- lkg.adts.get(tName).fold(Left(s"No ADT $tName in ${print_path(path)}"))(Right.apply)
              result <- adtDefn match {
                case AdtDefn(name, marker, DefnBody(Some(ctors), _, _, _)) => for {
                  // Checking shape of g
                  casesDefn <- g match {
                    case App(FamCases(Some(casesPath), casesName), Rec(_)) => for {
                      lkg <- getCompleteLinkage(casesPath)
                      result <- lkg.depot.get(casesName).fold(Left(s"No cases $casesName in ${print_path(path)}"))(Right.apply)
                    } yield result
                    case _ => Left(s"${print_exp(g)} is not a valid match argument.")
                  }
                  allCaseHandlerTypes <- collectAllCaseHandlerTypes(casesDefn)
                  caseHandlerOutTypes <- traverseMap(allCaseHandlerTypes) {
                    case FunType(_, outType) => Right(outType)
                    case t => Left(s"Invalid type ${print_type(t)} for case handler for cases ${casesDefn.name}")
                  }.map(_.values.toList)
                  outType <- unifyTypes(caseHandlerOutTypes)
                } yield outType
                case _ => Left("TODO cannot have cases in family that does not extend adt")
              }
            } yield result

            case t => Left(s"Cannot match on type ${print_type(t)}; not an ADT type.")
          }

        // All other cases
        case _ => Left(s"Expression ${print_exp(e)} does not type-check")
      }} match {
        case Left(msg) => Left(s"$msg\nIn expression ${print_exp(e)}")
        case result@Right(t) =>
          e.exprType = Some(t)
          result
      }

  def getInexactCompleteLinkage(p: Path): Either[String, Linkage] = {
    // Handles
    //
    // ____________________ L-Prog
    // K |- <prog> ~> L
    //
    // and
    //
    // K |- sp.A ~> L
    // ______________________ L-Self
    // K |- self(sp.A) ~> L
    val pathResolved0: Path = concretizePath0(Sp(relativizePath(p)))
    val pathResolved: Path = concretizePath(p)

    cache.get(pathResolved) match {
      case Some(lkg) => Right(lkg)
      case None => for {
        computedLkg <- computeInexactCompleteLinkage(pathResolved0)
      } yield { cache += pathResolved -> computedLkg; computedLkg }
    }
  }

  def getCompleteLinkage(p: Path): Either[String, Linkage] =
    getInexactCompleteLinkage(p).map(subExact(p))

  // K |- a ~> L
  // I = L.A
  // p = I.super
  // K |- p ~> L'
  // L' + I = L"
  // _________________________________ L-Nest
  // K |- a.A ~> L"
  def computeInexactCompleteLinkage(path: Path): Either[String, Linkage] = path match {
    case Sp(_) => throw new Exception("should only be called on Absolute paths")
    case AbsoluteFamily(pref, fam) => for {
      // L
      enclosingLkg <- getCompleteLinkage(pref)
      // I
      incompleteCurLkg <- enclosingLkg.nested.get(fam).fold(Left(s"TODO no such path $path"))(Right.apply)
      _ <- resolveImplicitPathsInSigs(incompleteCurLkg)
      // L'
      optSupLkg <- incompleteCurLkg.sup match {
        case None => Right(None)
        case Some(supP) => getInexactCompleteLinkage(supP).map(Some.apply)
      }
      incompleteUnfoldedCurLkg <- unfoldWildcards(path, incompleteCurLkg)
      result <- concatLinkages(Extends)(optSupLkg, incompleteUnfoldedCurLkg)
    } yield result
  }

  def unfoldWildcards(path: Path, lkg: Linkage): Either[String, Linkage] = for {
    depot <- traverseMap(lkg.depot) { casesDefn =>
      if (casesDefn.matchType.path==Some(Sp(lkg.self)) &&
        (casesDefn.t match {
          case FunType(_, RecType(fields)) if fields.contains("_") => true
          case _ => false
        }))
        for {
          wildcardCase <- casesDefn.casesBody match {
            case DefnBody(Some(Lam(_, _, Rec(fields))), _, _, _) => fields.get("_").toRight("expected _ case in body").map(Some.apply)
            case DefnBody(Some(x), _, _, _) => Left(s"unexpected shape $x")
            case DefnBody(None, _, _, _) => Right(None)
          }
          (wildcardVar, wildcardBody) = wildcardCase match {
            case Some(Lam(v, _, body)) => (Some(v), Some(body))
            case None => (None, None)
          }
          presentConstructors = casesDefn.casesBody match {
            case DefnBody(Some(Lam(_, _, Rec(fields))), _, _, _) => fields.keys.toSet - "_"
            case _ => Set.empty
          }
          adt <- lkg.adts.get(casesDefn.matchType.name).toRight(s"expected local ADT ${casesDefn.matchType.name}")
          constructors = adt.adtBody match {
            case DefnBody(Some(body), _, _, _) => body
            case DefnBody(None, _, _, allDefns) => allDefns.last
          }
          unfoldedCases = (wildcardVar, wildcardBody) match {
            case (Some(v), Some(b)) => 
              for {
                (c,t) <- constructors
                if !presentConstructors.contains(c)
              } yield (c -> Lam(v, t, b))
            case _ => Set.empty
          }
          (context, returnType, presentFields) = casesDefn.t match {
            case FunType(c, RecType(fields)) => (c,
              fields("_") match { case FunType(_, r) => r },
              fields - "_")
          }
          unfoldedTypes = for {
            (c,t) <- constructors
            if !presentConstructors.contains(c)
          } yield (c -> FunType(t, returnType))
          newT = FunType(context, RecType(presentFields ++ unfoldedTypes))
          newBody = casesDefn.casesBody match {
            case DefnBody(Some(Lam(v, t, Rec(fields))), _, _, _) =>
              Some(Lam(v, t, Rec((fields - "_") ++ unfoldedCases)))
            case _ => None
          }
          newCasesDefn = casesDefn match {
            case CasesDefn(name, matchType, oldTs, ts, marker, defn) =>
              CasesDefn(name, matchType, newT, replaceLast(ts, newT, oldTs), marker, (newBody, defn) match {
                case (Some(newBody), DefnBody(Some(oldBody), extendsFrom, furtherBindsFrom, allDefns)) =>
                  DefnBody(Some(newBody), extendsFrom, furtherBindsFrom, replaceLast(allDefns, newBody, oldBody))
                case _ => defn
              })
          }
        } yield newCasesDefn
      else Right(casesDefn)
    }
  } yield (lkg.copy(depot = depot))

  def replaceLast[A](xs: List[A], x: A, old: A): List[A] = {
    assert(xs.last==old)
    (x :: xs.reverse.tail).reverse
  }

  def resolveImplicitPathsInSigs(l: Linkage): Either[String, Unit] = {
    val curPath: Path = l.path
    for {
      _ <- traverseMap(l.types) {
        case TypeDefn(name, marker, typeBody) => for {
          _ <- typeBody match {
            case DefnBody(Some(RecType(fields)), extendsFrom, furtherBindsFrom, _) =>
              traverseMap(fields)(resolveImplicitPathsInType(l))
            case _ => Right(())
          }
          _ <- eitherFromList(typeBody.allDefns.map{case RecType(fields) =>
            traverseMap(fields)(resolveImplicitPathsInType(l))})
        } yield ()
      }
      _ <- traverseMap(l.adts) {
      case AdtDefn(name, marker, adtBody) => for {
        _ <- adtBody match {
          case DefnBody(Some(ctors), extendsFrom, furtherBindsFrom, _) =>
            traverseMap(ctors) { c =>
              traverseMap(c.fields)(resolveImplicitPathsInType(l))
            }
          case _ => Right(())
        }
        _ <- eitherFromList(adtBody.allDefns.map{ctors => traverseMap(ctors) { c =>
          traverseMap(c.fields)(resolveImplicitPathsInType(l))
        }})
      } yield ()
      }
      _ <- traverseMap(l.funs) {
        case FunDefn(name, t, _) => resolveImplicitPathsInType(l)(t)
      }
      _ <- traverseMap(l.depot) {
        case CasesDefn(name, matchType, t, ts, _, _) => for {
          _ <- resolveImplicitPathsInType(l)(matchType)
          _ <- resolveImplicitPathsInType(l)(t)
          _ <- eitherFromList(ts.map(resolveImplicitPathsInType(l)))
        } yield ()
     }
    } yield ()
  }

  // Recursively substitutes instances of a self by a path in type
  def subSelfByPathInPath(oldSelf: SelfPath, newPath: Path)(p: Path): Path = p match {
    case Sp(sp) if sp == oldSelf => newPath
    case Sp(Prog) => Sp(Prog)
    case Sp(SelfFamily(pref, name)) => Sp(SelfFamily(subSelfByPathInPath(oldSelf, newPath)(pref), name))
    case AbsoluteFamily(pref, name) => AbsoluteFamily(subSelfByPathInPath(oldSelf, newPath)(pref), name)
  }

  def subSelfByPathInType(oldSelf: SelfPath, newPath: Path)(t: Type): Type =
    mapPathInType(subSelfByPathInPath(oldSelf, newPath))(t)

  def subExact(p: Path)(lkg: Linkage): Linkage = p match {
    case Sp(sp) => lkg
    case p@AbsoluteFamily(pref, name) => {
      val f = subSelfByPathInPath(SelfFamily(pref, name), p)
      Linkage(
        f(lkg.path),
        lkg.self,
        lkg.sup.map(f),
        mapPathInLinkageTypes(f)(lkg.types),
        mapPathInLinkageDefaults(f)(lkg.defaults),
        mapPathInLinkageAdts(f)(lkg.adts),
        mapPathInLinkageFuns(f)(lkg.funs),
        mapPathInLinkageDepot(f)(lkg.depot),
        lkg.nested.view.mapValues(subExact(p)).toMap)
    }
  }

  def mapPathInLinkageTypes(f: Path => Path)(types: Map[String, TypeDefn]): Map[String, TypeDefn] =
    types.view
      .mapValues {
        case TypeDefn(name, marker, typeBody) => TypeDefn(
          name,
          marker,
          mapPathInDefnBody(typeBody) { t =>
            mapPathInType(f)(t).asInstanceOf[RecType]
          }
        )
      }
    .toMap

  def mapPathInLinkageDefaults(f: Path => Path)(defaults: Map[String, DefaultDefn]): Map[String, DefaultDefn] =
    defaults.view
      .mapValues {
        case DefaultDefn(name, marker, defaultBody) => DefaultDefn(
          name,
          marker,
          mapPathInDefnBody(defaultBody) { rec =>
            mapPathInExpression(f)(rec).asInstanceOf[Rec]
          }
        )
      }
      .toMap

  def mapPathInLinkageAdts(f: Path => Path)(adts: Map[String, AdtDefn]): Map[String, AdtDefn] =
    adts.view
      .mapValues {
        case AdtDefn(name, marker, adtBody) => AdtDefn(
          name,
          marker,
          mapPathInDefnBody(adtBody) { body =>
            body.view.mapValues(mapPathInType(f)(_).asInstanceOf[RecType]).toMap
          }
        )
      }
    .toMap

  def mapPathInLinkageFuns(f: Path => Path)(funs: Map[String, FunDefn]): Map[String, FunDefn] =
    funs.view
      .mapValues {
        case FunDefn(name, t, body) => FunDefn(
          name,
          mapPathInType(f)(t).asInstanceOf[FunType],
          mapPathInDefnBody(body)(mapPathInExpression(f))
        )
      }
      .toMap

  def mapPathInLinkageDepot(f: Path => Path)(depot: Map[String, CasesDefn]): Map[String, CasesDefn] =
    depot.view
      .mapValues {
        case CasesDefn(name, matchType, t, ts, marker, body) => CasesDefn(
          name,
          mapPathInType(f)(matchType).asInstanceOf[FamType],
          mapPathInType(f)(t).asInstanceOf[FunType],
          ts.map(mapPathInType(f)),
          marker,
          mapPathInDefnBody(body)(mapPathInExpression(f))
        )
      }
      .toMap

  // Recursively substitutes instances of `newSelf` for `oldSelf` in lkg
  // lkg [newSelf / oldSelf]
  def subSelf(newSelf: SelfPath, oldSelf: SelfPath)(lkg: Linkage): Linkage = Linkage(
    lkg.path,
    subSelfInSelfPath(newSelf, oldSelf)(lkg.self),
    lkg.sup.map(subSelfInPath(newSelf, oldSelf)),
    mapPathInLinkageTypes(subSelfInPath(newSelf, oldSelf))(lkg.types),
    mapPathInLinkageDefaults(subSelfInPath(newSelf, oldSelf))(lkg.defaults),
    mapPathInLinkageAdts(subSelfInPath(newSelf, oldSelf))(lkg.adts),
    mapPathInLinkageFuns(subSelfInPath(newSelf, oldSelf))(lkg.funs),
    mapPathInLinkageDepot(subSelfInPath(newSelf, oldSelf))(lkg.depot),
    lkg.nested.view.mapValues(subSelf(newSelf, oldSelf)).toMap
  )

  def subSelfInType(newSelf: SelfPath, oldSelf: SelfPath)(t: Type): Type =
    mapPathInType(subSelfInPath(newSelf, oldSelf))(t)

  def mapPathInExpression(f: Path => Path)(e: Expression): Expression = { val ep = e match {
    case Lam(v, t, body) => Lam(v, mapPathInType(f)(t), mapPathInExpression(f)(body))
    case FamFun(path, name) => FamFun(path.map(f), name)
    case FamCases(path, name) => FamCases(path.map(f), name)
    case App(e1, e2) => App(mapPathInExpression(f)(e1), mapPathInExpression(f)(e2))
    case Rec(fields) => Rec(fields.view.mapValues(mapPathInExpression(f)).toMap)
    case Proj(e, name) => Proj(mapPathInExpression(f)(e), name)
    case Inst(t, rec) => Inst(
      mapPathInType(f)(t).asInstanceOf[FamType],
      mapPathInExpression(f)(rec).asInstanceOf[Rec]
    )
    case InstADT(t, cname, rec) => InstADT(
      mapPathInType(f)(t).asInstanceOf[FamType],
      cname,
      mapPathInExpression(f)(rec).asInstanceOf[Rec]
    )
    case Match(e, g) => Match(mapPathInExpression(f)(e), mapPathInExpression(f)(g))
    case _ => e
  }
    ep.exprType = e.exprType.map(mapPathInType(f))
    ep
  }
  def mapPathInDefnBody[B](body: DefnBody[B])(subB: B => B): DefnBody[B] = {
    body.copy(defn = body.defn.map(subB), allDefns = body.allDefns.map(subB))
  }

  def subSelfInPath(newSelf: SelfPath, oldSelf: SelfPath)(p: Path): Path = p match {
    case Sp(sp) => Sp(subSelfInSelfPath(newSelf, oldSelf)(sp))
    case AbsoluteFamily(pref, fam) => AbsoluteFamily(subSelfInPath(newSelf, oldSelf)(pref), fam)
  }
  def subSelfInSelfPath(newSelf: SelfPath, oldSelf: SelfPath)(sp: SelfPath): SelfPath = {
    if sp == oldSelf then newSelf
    else sp match {
      case Prog => Prog
      case SelfFamily(pref, fam) => SelfFamily(subSelfInPath(newSelf, oldSelf)(pref), fam)
    }
  }

  // Replaces `extendsFrom` and `furtherBindsFrom` in `curDefnBody` with those of `inheritedDefnBody`
  // if they are not already defined (Some(_))
  def mergeDefnBody[B](inheritedDefnBody: DefnBody[B], curDefnBody: DefnBody[B]): DefnBody[B] = {
    DefnBody(
      curDefnBody.defn,
      lastSome(inheritedDefnBody.extendsFrom, curDefnBody.extendsFrom),
      lastSome(inheritedDefnBody.furtherBindsFrom, curDefnBody.furtherBindsFrom),
      inheritedDefnBody.allDefns ++ curDefnBody.allDefns
    )
  }

  // I.self = L".self
  // I.super = L".super
  // L = L' [I.self / L'.self]
  // L.NESTED + I.NESTED = L".NESTED
  // L.TYPES + I.TYPES = L".TYPES
  // L.DEFAULTS + I.DEFAULTS = L".DEFAULTS
  // L.ADTS + I.ADTS = L".ADTS
  // L.FUNS + I.FUNS = L".FUNS
  // L.CASES + I.CASES = L".CASES
  // ______________________________________________________ CAT_TOP
  // L' + I = L"
  // `l1InheritForm` is how things in `l1` are inherited in the resulting linkage
  def concatLinkages(l1InheritForm: InheritForm)(optL1: Option[Linkage], l2: Linkage): Either[String, Linkage] = optL1 match {
    case None => Right(l2)
    case Some(l1) =>
      val l1SelfSubbed =
        subSelf(l2.self, l1.self)(
          markInheritForm(l1InheritForm)(l1)
        )
      for {
        concatenatedTypes <- concatTypes(l1SelfSubbed.types, l2.types)
        concatenatedDefaults <- concatDefaults(l1SelfSubbed.defaults, l2.defaults)
        concatenatedAdts <- concatAdts(l1SelfSubbed.adts, l2.adts)
        concatenatedFuns <- concatFuns(l1SelfSubbed.funs, l2.funs)
        concatenatedCases <- concatCases(l1SelfSubbed.depot, l2.depot)
        concatenatedNested <- concatNested(l1SelfSubbed.nested, l2.nested)
      } yield Linkage(
        concretizePath(Sp(l2.self)),
        l2.self,
        l2.sup,
        concatenatedTypes,
        concatenatedDefaults,
        concatenatedAdts,
        concatenatedFuns,
        concatenatedCases,
        concatenatedNested
      )
  }

  // forall R, rdef, rdef',
  //     R = rdef in L'.TYPES -->
  //     R (+?)= rdef' notin I.TYPES -->
  //     R = rdef in L".TYPES
  //
  // forall R, rdef, rdef',
  //     R = rdef in I.TYPES -->
  //     R = rdef' notin L'.TYPES -->
  //     R = rdef in L".TYPES
  //
  // forall R, ext, rdef,
  //     R += ext in I.TYPES -->
  //     R = rdef in L'.TYPES -->
  //     rdef' = rdef + ext -->
  //     R = rdef' in L".TYPES
  // ____________________________________ CAT_TYPES
  // L'.TYPES + I.TYPES = L".TYPES
  def concatTypes(types1: Map[String, TypeDefn], types2: Map[String, TypeDefn]): Either[String, Map[String, TypeDefn]] =
    unionWithM(types1, types2) {
      // typeR should always equal _typeR since they are names of types indexed by the same type name key
      case (TypeDefn(typeR, _, rDefLPrime), TypeDefn(_typeR, PlusEq, rDefI)) =>
        Right(TypeDefn(typeR, PlusEq, mergeDefnBody(rDefLPrime, rDefI)))
      case _ => Left("TODO invalid type definition")
    }

  // forall D, def, def',
  //     D = def in L'.DEFAULTS -->
  //     D (+?)= def' notin I.DEFAULTS -->
  //     D = def in L".DEFAULTS
  //
  // forall D, def, def',
  //     D = def in I.DEFAULTS -->
  //     D = def' notin L'.DEFAULTS -->
  //     D = def in L".DEFAULTS
  //
  // forall D, ext, def,
  //     D += ext in I.DEFAULTS -->
  //     D = def in L'.DEFAULTS -->
  //     def' = def + ext -->
  //     D = def' in L".DEFAULTS
  // ____________________________________ CAT_DEFAULTS
  // L'.DEFAULTS + I.DEFAULTS = L".DEFAULTS
  def concatDefaults(defaults1: Map[String, DefaultDefn], defaults2: Map[String, DefaultDefn]): Either[String, Map[String, DefaultDefn]] =
    unionWithM(defaults1, defaults2) {
      case (DefaultDefn(typeR, _, defLPrime), DefaultDefn(_typeR, PlusEq, defI)) =>
        Right(DefaultDefn(typeR, PlusEq, mergeDefnBody(defLPrime, defI)))
      case _ => Left("TODO invalid default definition")
    }

  // forall R, adtdef, adtdef',
  //     R = adtdef in L'.ADTS -->
  //     R (+?)= adtdef' notin I.ADTS -->
  //     R = adtdef in L".ADTS
  //
  // forall R, adtdef, adtdef',
  //     R = adtdef in I.ADTS -->
  //     R = adtdef' notin L'.ADTS -->
  //     R = adtdef in L".ADTS
  //
  // forall R, adtext, adtdef,
  //     R += adtext in I.ADTS -->
  //     R = adtdef in L'.ADTS -->
  //     adtdef' = adtdef + adtext -->
  //     R = adtdef' in L".ADTS
  // ____________________________________ CAT_ADTS
  // L'.ADTS + I.ADTS = L".ADTS
  def concatAdts(adts1: Map[String, AdtDefn], adts2: Map[String, AdtDefn]): Either[String, Map[String, AdtDefn]] =
    unionWithM(adts1, adts2) {
      case (AdtDefn(adtR, _, adtDef), AdtDefn(_adtR, PlusEq, adtExt)) =>
        Right(AdtDefn(adtR, PlusEq, mergeDefnBody(adtDef, adtExt)))
      case (adtDefn1, adtDefn2) => Left(s"Invalid ADT definition ${adtDefn1}, $adtDefn2")
    }

  // forall f, T, fdef, fdef',
  //     f : T = fdef in L'.FUNS -->
  //     f : T = fdef' notin I.FUNS -->
  //     f : T = fdef in L".FUNS
  //
  // forall f, T, fdef, fdef',
  //     f : T = fdef in I.FUNS -->
  //     f : T = fdef' notin L'.FUNS -->
  //     f : T = fdef in L".FUNS
  //
  // forall f, T, T', fdef, fdef',
  //     f : T = fdef in L'.FUNS -->
  //     f : T = fdef' in I.FUNS -->
  //     f : T = fdef' in L".FUNS
  // ____________________________________ CAT_FUNS
  // L'.FUNS + I.FUNS = L".FUNS
  def concatFuns(funs1: Map[String, FunDefn], funs2: Map[String, FunDefn]): Either[String, Map[String, FunDefn]] =
    unionWithM(funs1, funs2) {
      case (FunDefn(funF, fType, fDefBody), FunDefn(_funF, fTypePrime, fDefPrimeBody)) if fType == fTypePrime =>
        Right(FunDefn(funF, fTypePrime, mergeDefnBody(fDefBody, fDefPrimeBody)))
      case (fDef1, fDef2) => Left(s"TODO invalid function definition: $fDef1 VS $fDef2")
    }

  // forall r, Tm, Tc, Tc', cdef, cdef',
  //     r <Tm>: Tc = cdef in L'.CASES -->
  //     r <Tm>: Tc' = cdef' notin I.CASES -->
  //     r <Tm>: Tc = cdef in L".CASES
  //
  // forall r, Tm, Tc, Tc', cdef, cdef',
  //     r <Tm>: Tc = cdef in I.CASES -->
  //     r <Tm>: Tc' = cdef' notin L'.CASES -->
  //     r <Tm>: Tc = cdef in L".CASES
  //
  // forall r, Tm, Tc_in, Tc_out, Tc'_in, Tc'_out, cdef, cdef',
  //     r <Tm>: Tc_in -> Tc_out = cdef in L'.CASES -->
  //     r <Tm>: Tc'_in -> Tc'_out = cdef' in I.CASES -->
  //     Tc"_in = Tc_in + Tc'_in -->
  //     Tc"_out = Tc'_out + Tc'_out -->
  //     cdef" = cdef + cdef' -->
  //     r <Tm>: Tc"_in -> Tc"_out  = cdef" in L".CASES
  // ____________________________________ CAT_CASES
  // L'.CASES + I.CASES = L".CASES
  def concatCases(depot1: Map[String, CasesDefn], depot2: Map[String, CasesDefn]): Either[String, Map[String, CasesDefn]] =
    unionWithM(depot1, depot2) {
      case ( CasesDefn(casesName, prevMatchType, prevT, prevTs, _, prevCasesDefn)
           , CasesDefn(_casesName, curMatchType, curT, curTs, PlusEq, curCasesDefn)
           ) if sameFamType(prevMatchType, curMatchType) => for {
        resultT <- (prevT, curT) match {
          case (RecType(_), RecType(_)) => Right(curT)
          case (FunType(RecType(prevFields), RecType(_)), FunType(RecType(curFields), curOutT@RecType(_))) =>
            // TODO: curFields cannot have a field overwriting one in prevFields with different type?
            Right(FunType(RecType(prevFields ++ curFields), curOutT))
          case x => Left(s"Invalid cases definition: expected record or function type: $x")
        }
        // For implementation purposes, we do not absorb inherited cases directly.
        // The result `DefnBody` is instead marked with information about where it inherits from,
        // which is used to look up those other cases recursively
      } yield CasesDefn(casesName, curMatchType, resultT, prevTs ++ curTs, PlusEq, mergeDefnBody(prevCasesDefn, curCasesDefn))
      case x => Left(s"Invalid cases definition ${x._1.name}: expected += and ${print_type(concretizeType(x._1.matchType))} == ${print_type(concretizeType(x._2.matchType))}")
    }

  def sameFamType(ty1: FamType, ty2: FamType): Boolean = ty1.name == ty2.name && ((ty1.path, ty2.path) match {
    case (Some(p1), Some(p2)) => concretizePath(p1)==concretizePath(p2)
    case _ => true
  })

  // forall A,
  //     L'.A in L'.NESTED -->
  //     I.A notin I.NESTED -->
  //     L'.A in L".NESTED
  //
  // forall A,
  //     I.A in I.NESTED -->
  //     L'.A notin L'.NESTED -->
  //     I.A in L".NESTED
  //
  // forall A,
  //     I.A in I.NESTED -->
  //     L'.A in L'.NESTED -->
  //     K |- L'.A.self ~> L -->
  //     L + I.A = L".A -->
  //     L".A in L".NESTED
  // ______________________________________________ CAT_LINKS
  // L'.NESTED + I.NESTED = L".NESTED
  def concatNested(nested1: Map[String, Linkage], nested2: Map[String, Linkage]): Either[String, Map[String, Linkage]] =
    unionWithM(nested1, nested2) { (lkgLPrime_A, lkgI_A) =>
      concatLinkages(FurtherBinds)(Some(lkgLPrime_A), lkgI_A)
    }
}
