import famfun._
import PrettyPrint.*

object type_checking {
  val K: scala.collection.mutable.Map[Path, Linkage] = scala.collection.mutable.Map.empty

  def initK(progLkg: Linkage): Unit = {
    K.clear()
    K += Sp(Prog) -> progLkg
  }

  def unionWith[K, V](m1: Map[K, V], m2: Map[K, V])(f: (V, V) => V)(implicit ordK: Ordering[K]): Map[K, V] = {
    // l1 and l2 are sorted
    def merge(l1: List[(K, V)], l2: List[(K, V)]): List[(K, V)] = (l1, l2) match {
      case (Nil, ys) => ys
      case (xs, Nil) => xs
      case ((x@(xKey, xVal)) :: xs, (y@(yKey, yVal)) :: ys) =>
        if ordK.lt(xKey, yKey) then
          x :: merge(xs, l2)
        else if ordK.gt(xKey, yKey) then
          y :: merge(l1, ys)
        else
          (xKey, f(xVal, yVal)) :: merge(xs, ys)
    }
    merge(m1.toList.sortBy(_._1), m2.toList.sortBy(_._1)).toMap
  }

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

  def collectAllDefns[C, B, R](defnContainer: C)
                              (defnFromContainer: C => DefnBody[B])
                              (fromLinkage: Linkage => C)
                              (toResult: C => R)
                              (emptyResult: R)
                              (concatResults: (R, R) => R): R = {
    val visitedPaths: scala.collection.mutable.Set[Path] = scala.collection.mutable.Set.empty

    def collectAllDefnsHelp(defnContainer: C): R = {
      val defnBody = defnFromContainer(defnContainer)
      val extendsDefns: R = defnBody.extendsFrom match {
        case Some(p) if !visitedPaths.contains(p) =>
          visitedPaths += p
          val extendsDefnContainer = fromLinkage(getCompleteLinkage(p))
          collectAllDefnsHelp(extendsDefnContainer)
        case _ => emptyResult
      }
      val furtherBindsDefns: R = defnBody.furtherBindsFrom match {
        case Some(p) if !visitedPaths.contains(p) =>
          visitedPaths += p
          val furtherBindsDefnContainer = fromLinkage(getCompleteLinkage(p))
          collectAllDefnsHelp(furtherBindsDefnContainer)
        case _ => emptyResult
      }
      val curDefns: R = toResult(defnContainer)

      concatResults(concatResults(extendsDefns, furtherBindsDefns), curDefns)
    }
    collectAllDefnsHelp(defnContainer)
  }

  def collectAllConstructors(adtDefn: AdtDefn): Map[String, RecType] = {
    collectAllDefns(adtDefn)(_.adtBody) { lkg =>
      lkg.adts
        .getOrElse(adtDefn.name, throw new Exception(s"${lkg.self} should contain an ADT definition for ${adtDefn.name} by construction"))
    } { _.adtBody.defn.getOrElse(Map.empty) } (Map.empty) { _ ++ _ }
  }

  def collectAllNamedTypeFields(typeDefn: TypeDefn): Map[String, Type] = {
    collectAllDefns(typeDefn)(_.typeBody) { lkg =>
      lkg.types
        .getOrElse(typeDefn.name, throw new Exception(s"${lkg.self} should contain a type definition for ${typeDefn.name} by construction"))
    } { _.typeBody.defn.map(_.fields).getOrElse(Map.empty) } (Map.empty) { _ ++ _ }
  }

  def collectAllCaseHandlerTypes(casesDefn: CasesDefn): Either[String, Map[String, Type]] = {
    collectAllDefns(casesDefn)(_.casesBody) { lkg =>
      lkg.depot
        .getOrElse(casesDefn.name, throw new Exception(s"${lkg.self} should contain a cases definition for ${casesDefn.name} by construction"))
    } { cDefn => cDefn.t match {
      case RecType (cfTypes) => Right (cfTypes)
      case FunType (RecType (_), RecType (cfTypes)) => Right (cfTypes)
      case _ => Left (s"Invalid shape for cases type: ${print_type(cDefn.t)}")
    }} (Right(Map.empty)) { (result1, result2) => for { m1 <- result1; m2 <- result2 } yield m1 ++ m2 }
  }

  def unifyTypes(types: List[Type]): Either[String, Type] = types match {
    case Nil => Left("No types given to unify")
    case t :: ts => ts.foldLeft(Right(resolveType(t)).withLeft[String]) { (eAccType, curType) =>
      eAccType.flatMap { accType =>
        val resolvedAccType = resolveType(accType)
        val resolvedCurType = resolveType(curType)
        if isSubtype(resolvedAccType, resolvedCurType) then Right(resolvedCurType)
        else if isSubtype(resolvedCurType, resolvedAccType) then Right(resolvedAccType)
        else Left(s"Failed to unify types: ${types.map(print_type).mkString(", ")}")
      }
    }
  }

  def wf(t: Type): Boolean = t match {
    // _________________ WF_Num
    // K |-  WF(N)
    case N => true

    // _________________ WF_Bool
    // K |-  WF(B)
    case B => true

    // K |- a ~> L
    // R in L.TYPES
    // _________________ WF_Member
    // K |- WF(a.R)
    case FamType(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      lkg.types.contains(name) || lkg.adts.contains(name)

    // K |- WF(T)
    // K |- WF(T')
    // ____________________ WF_Arrow
    // K |- WF(T -> T')
    case FunType(t1, t2) => wf(t1) && wf(t2)

    // forall i, K |- WF(T_i)
    // forall i j, i != j --> f_i != f_j
    // ___________________________________WF_RecordType
    // K |- WF({(f_i: T_i)*})
    case RecType(m) => m.forall { case (_, t) => wf(t) }

    case _ => false
  }

  def isSubtype(t1: Type, t2: Type): Boolean = {
    def isSubtypeResolved(t1: Type, t2: Type): Boolean = {
      // _____________ Sub-Refl
      // K |- T <: T
      t1 == t2 || ((t1, t2) match {
        // K |- a ~> L
        // R = T in L.TYPES
        // K |- T <: T'
        // __________________ Sub-Fam
        // K |- a.R <: T'
        case (FamType(Some(a), r), tPrime) =>
          val aLkg = getCompleteLinkage(a)
          aLkg.types.get(r) match {
            case None =>
              aLkg.adts.get(r) match {
                case None => throw new Exception(s"No such type ${print_type(t1)}")
                case Some(_) => false
              }
            case Some(tTypeDefn) =>
              val t = RecType(collectAllNamedTypeFields(tTypeDefn))
              isSubtype(t, tPrime)
          }

        // K |- T1 <: S1
        // K |- S2 <: T2
        // _________________________ Sub-Fun
        // K |- S1 -> S2 <: T1 -> T2
        case (FunType(s1, s2), FunType(t1, t2)) =>
          isSubtype(t1, s1) && isSubtype(s2, t2)

        // forall j,
        //     (exists T',
        //         K |- T' <: T_j /\ (f_j: T') in {(f_i: T_i)*})
        // _______________________________________________________ Sub-Rec
        // K |- {(f_i: T_i)*} <: {(f_j: T_j)*}
        case (RecType(fis), RecType(fjs)) => fjs.forall { (fj, tj) =>
          fis.get(fj) match {
            case None => false
            case Some(ti) => isSubtype(ti, tj)
          }
        }

        case _ => false
      })
    }

    isSubtypeResolved(resolveType(t1), resolveType(t2))
  }

  def traverseWithKeyMap[K, V, E, W](m: Map[K, V])(f: (K, V) => Either[E, W]): Either[E, Map[K, W]] = {
    val kvpList: List[(K, V)] = m.toList
    kvpList.foldLeft(Right(List.empty[(K, W)]).withLeft[E]) {
      case (a, (curKey, curVal)) => for {
        accList <- a
        curValApplied <- f(curKey, curVal)
      } yield (curKey, curValApplied) :: accList
    }.map(_.toMap)
  }
  def traverseMap[K, V, E, W](m: Map[K, V])(f: V => Either[E, W]): Either[E, Map[K, W]] = {
    traverseWithKeyMap(m)((_: K, v: V) => f(v))
  }

  // TODO: check whether a self path is valid
  //   ie: reject Family X { Family Y { val f: self(Z).R -> B = ... } } even if Family Z exists
  def typeCheckLinkage(l: Linkage): Either[String, Unit] = {
    val completeL = getCompleteLinkage(l.path)
    val curPath = resolvePath(completeL.path)
    for {
      //completeL.defaults.values.forall(typeCheckDefaults)
      _ <- traverseMap(completeL.funs)(typeCheckFunDefns(curPath))
      _ <- traverseMap(completeL.depot)(typeCheckCasesDefns(curPath))
      _ <- traverseMap(completeL.nested)(typeCheckLinkage)
    } yield ()
  }

  def typeCheckFunDefns(curPath: Path)(f: FunDefn): Either[String, Unit] = f.funBody match {
    case DefnBody(None, _, _) => Right(())
    case DefnBody(Some(defn), _, _) =>
      typeOfExpression(Map.empty)(defn).flatMap { defnType =>
        if !isSubtype(defnType, f.t) then
          Left(
            s"""Type mismatch error for function `${f.name}` in ${print_path(curPath)}:
               |Found:    ${print_type(defnType)}
               |Required: ${print_type(f.t)}
               |""".stripMargin
          )
        else Right(())
      }
  }

  def typeCheckCasesDefns(curPath: Path)(c: CasesDefn): Either[String, Unit] = {
    for {
      allCaseHandlerTypes <- collectAllCaseHandlerTypes(c)
      caseHandlerTypesAsCtors <- traverseMap(allCaseHandlerTypes) {
        case FunType(RecType(fields), _) => Right(RecType(fields))
        case t => Left(s"Invalid case handler type: ${print_type(t)}")
      }
      matchAdtDefn <-
        c.matchType.path
          .flatMap(getCompleteLinkage(_).adts.get(c.matchType.name))
          .fold(Left(s"No ADT ${c.matchType.name} in ${print_path(c.matchType.path.get)}"))(Right.apply)
      allCtors = collectAllConstructors(matchAdtDefn)

      // Exhaustive check
      _ <-
        if caseHandlerTypesAsCtors == allCtors then Right(())
        else Left(s"Cases ${c.name} in ${print_path(curPath)} is non-exhaustive.")
      caseHandlerOutTypes <- traverseMap(allCaseHandlerTypes) {
        case FunType(_, outType) => Right(outType)
        case t => Left(s"Invalid type ${print_type(t)} for case handler for cases ${c.name} in ${print_path(curPath)}")
      }.map(_.values.toList)
      // Consistent result type check
      _ <- unifyTypes(caseHandlerOutTypes).left.map { unifyErrMsg =>
        s"""Inconsistent output types for case handlers for cases ${c.name} in ${print_path(curPath)}:
            |$unifyErrMsg
            |""".stripMargin
      }

      // Check body
      _ <- c.casesBody.defn match {
        case None => Right(())
        case Some(defn) => typeOfExpression(Map.empty)(defn).flatMap { defnType =>
          if isSubtype(defnType, c.t) then Right(())
          else Left(
            s"""Type mismatch error for cases `${c.name}` in ${print_path(curPath)}:
               |Found:    ${print_type(defnType)}
               |Required: ${print_type(c.t)}
               |""".stripMargin
          )
        }
      }
    } yield ()
  }

  // Exceptions or Option?
  def typeOfExpression(G: Map[String, Type])(e: Expression): Either[String, Type] = e match {
    // _________________ T_Num
    // K, G |- n : N
    case Nexp(n) => Right(N)

    // _________________ T_Bool
    // K, G |- b : B
    case Bexp(b) => Right(B)

    // x: T \in G
    // ________________T_Var
    // K, G |- x : T
    case Var(x) => G.get(x).fold(Left(s"Variable $x unbound"))(Right.apply)

    // K |- WF(T)
    // K, (x : T, G) |- body : T'
    // _____________________________________ T_Lam
    // K, G |- lam (x : T). body : T -> T'
    case Lam(Var(x), xType, body) =>
      if wf(xType) then typeOfExpression(G + (x -> xType))(body).map(FunType(xType, _))
      else Left(s"Type $xType is not well-formed")

    // K, G |- e : T
    // K, G |- g : T -> T'
    // _____________________ T_App
    // K, G |- g e : T'
    case App(e1, e2) =>
      typeOfExpression(G)(e1).flatMap { // type e1
        case FunType(iType, oType) =>
          typeOfExpression(G)(e2).flatMap { e2Type =>
            if isSubtype(e2Type, iType) then Right(oType)
            else {
              val e1Pretty = print_exp(e1)
              val e2Pretty = print_exp(e2)
              Left(
                s"""Cannot apply $e1Pretty to $e2Pretty;
                   |$e1Pretty expects an argument of type $iType but got one of type $e2Type.
                   |""".stripMargin
              )
            }
          }
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
      traverseMap(fields)(typeOfExpression(G)).map(RecType.apply)

    // K, G |- e : {(f': T')*}
    // (f: T) in (f': T')*
    // _________________________ T_Proj
    // K, G |- e.f : T
    case Proj(e, f) =>
      typeOfExpression(G)(e).flatMap {
        case RecType(fTypes) =>
          fTypes.get(f).fold(Left("TODO no such field"))(Right.apply)
        // if we have an instance of a type, the inferred type will be a famtype
        case FamType(Some(p), typeName) =>
          val lkg = getCompleteLinkage(p)
          lkg.types.get(typeName).fold(Left("TODO no such named type"))(Right.apply).flatMap { typeDefn =>
            val allTypeFields: Map[String, Type] = collectAllNamedTypeFields(typeDefn)
            allTypeFields.get(f).fold(Left("TODO no such field"))(Right.apply)
          }
        case _ => Left("TODO invalid projection")
      }

    // K |- a ~> L
    // m : (T -> T') = lam (x : T). body in L.FUNS
    // _______________________________________________ T_FamFun
    // K, G |- a.m : T -> T'
    case FamFun(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      lkg.funs.get(name).fold(Left(s"No such function $name"))(Right.apply).map {
        case FunDefn(_, fType, _) => fType
      }

    // K |- a ~> L
    // r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*} =
    //         lam (x: {(f_i:T_i)*}). body in L.CASES
    // _______________________________________________________________ T_Cases
    // K, G |- a.r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*}
    case FamCases(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      // Validity of type for the defined `cases` will be checked at the top level (ie, match type works with defnType)
      lkg.depot.get(name).fold(Left("TODO no such cases"))(Right.apply).map {
        case CasesDefn(_, _, casesType, _, _) => casesType
      }

    // K |- a ~> L
    // R = {(f_i: T_i)*} in L.TYPES
    // forall i,
    //     K, G |- e_i : T_i
    // ______________________________________ T_Constructor
    // K, G |- a.R({(f_i = e_i)*}) : a.R
    case Inst(famType@FamType(Some(path), typeName), rec) =>
      val lkg = getCompleteLinkage(path)
      lkg.types.get(typeName).fold(Left(s"No type $typeName in $path"))(Right.apply).flatMap { typeDefn =>
        val allTypeFields: Map[String, Type] = collectAllNamedTypeFields(typeDefn)

        traverseWithKeyMap(rec.fields) { (f: String, e: Expression) => // typeCheck all fields wrt linkage definition
          allTypeFields.get(f).fold(Left("TODO no such field"))(Right.apply).flatMap { fieldType =>
            typeOfExpression(G)(e).flatMap { eType =>
              if isSubtype(eType, fieldType) then Right(())
              else Left("TODO field types in instance don't match")
            }
          }
        }.map(_ => famType)
      }

    //  R = \overline{C' {(f': T')*}} in {{a}}
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(famType@FamType(Some(path), tName), cname, rec) =>
      for {
        instFields <- traverseMap(rec.fields)(typeOfExpression(G))
        instFieldsResolved = instFields.view.mapValues(resolveType).toMap
        lkg = getCompleteLinkage(path)
        adtDefn <- lkg.adts.get(tName).fold(Left(s"No ADT $tName in ${print_path(path)}")) (Right.apply)
        allCtors = collectAllConstructors(adtDefn)
        ctorRecType <- allCtors.get(cname).fold(Left(s"No constructor $cname for $tName in ${print_path(path)}"))(Right.apply)
        ctorFieldsResolved = ctorRecType.fields.view.mapValues(resolveType).toMap
        // we do not allow subtyping within ADT records right now
        result <-
          if instFieldsResolved == ctorFieldsResolved then Right(famType)
          else Left(
            s"""Mismatching field types in ADT instance for $tName with constructor $cname in ${print_path(path)}:"
               |Instance field types:    ${print_type(RecType(instFieldsResolved))}
               |Constructor field types: ${print_type(RecType(ctorFieldsResolved))}
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
      typeOfExpression(G)(e).flatMap {
        case FamType(Some(path), tName) =>
          val lkg = getCompleteLinkage(path)
          // look up the name of the ADT type in the linkage
          lkg.adts.get(tName).fold(Left(s"No ADT $tName in ${print_path(path)}"))(Right.apply).flatMap {
            case AdtDefn(name, marker, DefnBody(Some(ctors), _, _)) => for {
              // Checking shape of g
              casesDefn <- g match {
                case App(FamCases(Some(casesPath), casesName), Rec(_)) =>
                  val lkg = getCompleteLinkage(casesPath)
                  lkg.depot.get(casesName).fold(Left(s"No cases $casesName in ${print_path(path)}"))(Right.apply)
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
        case t => Left(s"Cannot match on type ${print_type(t)}; not an ADT type.")
      }

    // All other cases
    case _ => Left(s"Expression ${print_exp(e)} does not type-check")
  }

  def getCompleteLinkage(p: Path): Linkage = {
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
    val pathResolved: Path = resolvePath(p)

    K.get(pathResolved) match {
      case Some(lkg) => lkg
      case None =>
        val computedLkg = computeCompleteLinkage(pathResolved)
        K += pathResolved -> computedLkg
        computedLkg
    }
  }

  // K |- a ~> L
  // I = L.A
  // p = I.super
  // K |- p ~> L'
  // L' + I = L"
  // _________________________________ L-Nest
  // K |- a.A ~> L"
  def computeCompleteLinkage(path: Path): Linkage = path match {
    case Sp(_) => throw new Exception("computeCompleteLinkage should only be called on Absolute paths")
    case AbsoluteFamily(pref, fam) =>
      // L
      val enclosingLkg = getCompleteLinkage(pref)
      // I
      val incompleteCurLkg = enclosingLkg.nested.getOrElse(fam, throw new Exception(s"TODO no such path $path"))
      // L'
      val optSupLkg = incompleteCurLkg.sup.map(getCompleteLinkage)

      concatLinkages(Extends)(optSupLkg, incompleteCurLkg)
  }

  // Recursively substitutes instances of `newSelf` for `oldSelf` in lkg
  // lkg [newSelf / oldSelf]
  def subSelf(newSelf: SelfPath, oldSelf: SelfPath)(lkg: Linkage): Linkage = Linkage(
    lkg.path,
    subSelfInSelfPath(newSelf, oldSelf)(lkg.self),
    lkg.sup.map(subSelfInPath(newSelf, oldSelf)),
    lkg.types.view
      .mapValues {
        case TypeDefn(name, marker, typeBody) => TypeDefn(
          name,
          marker,
          subSelfInDefnBody(newSelf, oldSelf)(typeBody){ (ns, os) => t =>
            subSelfInType(ns, os)(t).asInstanceOf[RecType]
          }
        )
      }
      .toMap,
    lkg.defaults.view
      .mapValues {
        case (marker, rec) => marker -> subSelfInExpression(newSelf, oldSelf)(rec).asInstanceOf[Rec]
      }
      .toMap,
    lkg.adts.view
      .mapValues {
        case AdtDefn(name, marker, adtBody) => AdtDefn(
          name,
          marker,
          subSelfInDefnBody(newSelf, oldSelf)(adtBody) { (ns, os) => body =>
            body.view.mapValues(subSelfInType(ns, os)(_).asInstanceOf[RecType]).toMap
          }
        )
      }
      .toMap,
    lkg.funs.view
      .mapValues {
        case FunDefn(name, t, body) => FunDefn(
          name,
          subSelfInType(newSelf, oldSelf)(t).asInstanceOf[FunType],
          subSelfInDefnBody(newSelf, oldSelf)(body)(subSelfInExpression)
        )
      }
      .toMap,
    lkg.depot.view
      .mapValues {
        case CasesDefn(name, matchType, t, marker, body) => CasesDefn(
          name,
          subSelfInType(newSelf, oldSelf)(matchType).asInstanceOf[FamType],
          subSelfInType(newSelf, oldSelf)(t).asInstanceOf[FunType],
          marker,
          subSelfInDefnBody(newSelf, oldSelf)(body)(subSelfInExpression)
        )
      }
      .toMap,
    lkg.nested.view.mapValues(subSelf(newSelf, oldSelf)).toMap
  )
  def subSelfInType(newSelf: SelfPath, oldSelf: SelfPath)(t: Type): Type = t match {
    case FamType(path, name) => FamType(path.map(subSelfInPath(newSelf, oldSelf)), name)
    case FunType(inType, outType) => FunType(subSelfInType(newSelf, oldSelf)(inType), subSelfInType(newSelf, oldSelf)(outType))
    case RecType(fields) => RecType(fields.view.mapValues(subSelfInType(newSelf, oldSelf)).toMap)
    case _ => t
  }
  def subSelfInExpression(newSelf: SelfPath, oldSelf: SelfPath)(e: Expression): Expression = e match {
    case Lam(v, t, body) => Lam(v, subSelfInType(newSelf, oldSelf)(t), subSelfInExpression(newSelf, oldSelf)(body))
    case FamFun(path, name) => FamFun(path.map(subSelfInPath(newSelf, oldSelf)), name)
    case FamCases(path, name) => FamCases(path.map(subSelfInPath(newSelf, oldSelf)), name)
    case App(e1, e2) => App(subSelfInExpression(newSelf, oldSelf)(e1), subSelfInExpression(newSelf, oldSelf)(e2))
    case Rec(fields) => Rec(fields.view.mapValues(subSelfInExpression(newSelf, oldSelf)).toMap)
    case Proj(e, name) => Proj(subSelfInExpression(newSelf, oldSelf)(e), name)
    case Inst(t, rec) => Inst(
      subSelfInType(newSelf, oldSelf)(t).asInstanceOf[FamType],
      subSelfInExpression(newSelf, oldSelf)(rec).asInstanceOf[Rec]
    )
    case InstADT(t, cname, rec) => InstADT(
      subSelfInType(newSelf, oldSelf)(t).asInstanceOf[FamType],
      cname,
      subSelfInExpression(newSelf, oldSelf)(rec).asInstanceOf[Rec]
    )
    case Match(e, g) => Match(subSelfInExpression(newSelf, oldSelf)(e), subSelfInExpression(newSelf, oldSelf)(g))
    case _ => e
  }
  def subSelfInDefnBody[B](newSelf: SelfPath, oldSelf: SelfPath)(body: DefnBody[B])
                          (subB: (SelfPath, SelfPath) => B => B): DefnBody[B] = {
    body.copy(defn = body.defn.map(subB(newSelf, oldSelf)))
  }
  def subSelfInPath(newSelf: SelfPath, oldSelf: SelfPath)(p: Path): Path = p match {
    case Sp(sp) => Sp(subSelfInSelfPath(newSelf, oldSelf)(sp))
    case AbsoluteFamily(pref, fam) => AbsoluteFamily(subSelfInPath(newSelf, oldSelf)(pref), fam)
  }
  def subSelfInSelfPath(newSelf: SelfPath, oldSelf: SelfPath)(sp: SelfPath): SelfPath = {
    if sp == oldSelf then newSelf
    else sp match {
      case Prog => Prog
      case SelfFamily(pref, fam) => SelfFamily(subSelfInSelfPath(newSelf, oldSelf)(pref), fam)
    }
  }

  // Replaces `extendsFrom` and `furtherBindsFrom` in `curDefnBody` with those of `inheritedDefnBody`
  // if they are not already defined (Some(_))
  def mergeDefnBody[B](inheritedDefnBody: DefnBody[B], curDefnBody: DefnBody[B]): DefnBody[B] = {
    def lastSome[T](opt1: Option[T], opt2: Option[T]): Option[T] = opt2 match {
      case None => opt1
      case Some(_) => opt2
    }
    DefnBody(
      curDefnBody.defn,
      lastSome(inheritedDefnBody.extendsFrom, curDefnBody.extendsFrom),
      lastSome(inheritedDefnBody.furtherBindsFrom, curDefnBody.furtherBindsFrom)
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
  def concatLinkages(l1InheritForm: InheritForm)(optL1: Option[Linkage], l2: Linkage): Linkage = optL1 match {
    case None => l2
    case Some(l1) =>
      val l1SelfSubbed =
        subSelf(l2.self, l1.self)(
          markInheritForm(l1InheritForm)(l1)
        )
      Linkage(
        resolvePath(Sp(l2.self)),
        l2.self,
        l2.sup,
        concatTypes(l1SelfSubbed.types, l2.types),
        l2.defaults, // TODO: bring this back; concatDefaults(l1SelfSubbed.defaults, l2.defaults),
        concatAdts(l1SelfSubbed.adts, l2.adts),
        concatFuns(l1SelfSubbed.funs, l2.funs),
        concatCases(l1SelfSubbed.depot, l2.depot),
        concatNested(l1SelfSubbed.nested, l2.nested)
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
  def concatTypes(types1: Map[String, TypeDefn], types2: Map[String, TypeDefn]): Map[String, TypeDefn] = unionWith(types1, types2) {
    // typeR should always equal _typeR since they are names of types indexed by the same type name key
    case (TypeDefn(typeR, _, rDefLPrime), TypeDefn(_typeR, PlusEq, rDefI)) =>
      TypeDefn(typeR, PlusEq, mergeDefnBody(rDefLPrime, rDefI))
    case _ => throw new Exception("TODO invalid type definition")
  }

  def concatDefaults(defaults1: Map[String, (Marker, Rec)], defaults2: Map[String, (Marker, Rec)]): Map[String, (Marker, Rec)] = ???

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
  def concatAdts(adts1: Map[String, AdtDefn], adts2: Map[String, AdtDefn]): Map[String, AdtDefn] = unionWith(adts1, adts2) {
    case (AdtDefn(adtR, _, adtDef), AdtDefn(_adtR, PlusEq, adtExt)) =>
      AdtDefn(adtR, PlusEq, mergeDefnBody(adtDef, adtExt))
    case (adtDefn1, adtDefn2) => throw new Exception(s"Invalid ADT definition ${adtDefn1}, $adtDefn2")
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
  def concatFuns(funs1: Map[String, FunDefn], funs2: Map[String, FunDefn]): Map[String, FunDefn] = unionWith(funs1, funs2) {
    case (FunDefn(funF, fType, fDefBody), FunDefn(_funF, fTypePrime, fDefPrimeBody)) if fType == fTypePrime =>
      FunDefn(funF, fTypePrime, mergeDefnBody(fDefBody, fDefPrimeBody))
    case _ => throw new Exception("TODO invalid function definition")
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
  def concatCases(depot1: Map[String, CasesDefn], depot2: Map[String, CasesDefn]): Map[String, CasesDefn] = unionWith(depot1, depot2) {
    // TODO: check match types are consistent somehow?
    case ( CasesDefn(casesName, prevMatchType, prevT, _, prevCasesDefn)
         , CasesDefn(_casesName, curMatchType, curT, PlusEq, curCasesDefn)
         ) =>
      val resultT: Type = (prevT, curT) match {
        case (RecType(_), RecType(_)) => curT
        case (FunType(RecType(prevFields), RecType(_)), FunType(RecType(curFields), curOutT@RecType(_))) =>
          // TODO: curFields cannot have a field overwriting one in prevFields with different type?
          FunType(RecType(prevFields ++ curFields), curOutT)
        case _ => throw new Exception("TODO invalid cases definition")
      }
      // For implementation purposes, we do not absorb inherited cases directly.
      // The result `DefnBody` is instead marked with information about where it inherits from,
      // which is used to look up those other cases recursively
      CasesDefn(casesName, curMatchType, resultT, PlusEq, mergeDefnBody(prevCasesDefn, curCasesDefn))
    case _ => throw new Exception("TODO invalid cases definition")
  }

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
  def concatNested(nested1: Map[String, Linkage], nested2: Map[String, Linkage]): Map[String, Linkage] = unionWith(nested1, nested2) {
    (lkgLPrime_A, lkgI_A) =>
      concatLinkages(FurtherBinds)(Some(lkgLPrime_A), lkgI_A)
  }
}
