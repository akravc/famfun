import famfun._

object type_checking {
  val K: scala.collection.mutable.Map[Path, Linkage] = scala.collection.mutable.Map.empty

  def initK(progLkg: Linkage) = {
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
  // Marks definitions in the top-level of l as extended or further bound
  // TODO possible optimization: don't change if body.defn is None
  def markInheritForm(form: InheritForm, l: Linkage): Linkage = {
    // Sets `extendsFrom` or `furtherBindsFrom` to the self(?) path of `l` based on `form` (sets the other to None),
    // and makes `defn` `None` as either:
    //   1. a new definition will extend it
    //   2. it will be inherited only.
    // This, along with when things are extended and further bound, are handled by the concatenation functions.
    def markBody[B](body: DefnBody[B]): DefnBody[B] = form match {
      case Extends => DefnBody(None, Some(resolvePath(Sp(l.self))), None) // TODO: or l.path?
      case FurtherBinds => DefnBody(None, None, Some(resolvePath(Sp(l.self))))
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
      }.toMap
    )
  }

  def collectAllDefns[B, R](defnBody: DefnBody[B])
                           (fromLinkage: Linkage => DefnBody[B])
                           (toResult: B => R)
                           (emptyResult: R)
                           (concatResults: (R, R) => R): R = {
    val visitedPaths: scala.collection.mutable.Set[Path] = scala.collection.mutable.Set.empty

    def collectAllDefnsHelp(defnBody: DefnBody[B]): R = {
      val extendsDefns: R = defnBody.extendsFrom match {
        case Some(p) if !visitedPaths.contains(p) =>
          visitedPaths += p
          val extendsDefnBody = fromLinkage(getCompleteLinkage(p))
          collectAllDefnsHelp(extendsDefnBody)
        case _ => emptyResult
      }
      val furtherBindsDefns: R = defnBody.furtherBindsFrom match {
        case Some(p) if !visitedPaths.contains(p) =>
          visitedPaths += p
          val furtherBindsDefnBody = fromLinkage(getCompleteLinkage(p))
          collectAllDefnsHelp(furtherBindsDefnBody)
        case _ => emptyResult
      }
      val curDefns: R = defnBody.defn.map(toResult)getOrElse(emptyResult)

      concatResults(concatResults(extendsDefns, furtherBindsDefns), curDefns)
    }
    collectAllDefnsHelp(defnBody)
  }

  def collectAllConstructors(adtDefn: AdtDefn): Map[String, RecType] = {
    val AdtDefn(name, _, adtBody) = adtDefn
    collectAllDefns(adtBody) { lkg =>
      lkg.adts
        .getOrElse(name, throw new Exception(s"${lkg.self} should contain an ADT definition for $name by construction"))
        .adtBody
    } { m => m } (Map.empty) { _ ++ _ }
  }

  def collectAllNamedTypeFields(typeDefn: TypeDefn): Map[String, Type] = {
    val TypeDefn(name, _, typeBody) = typeDefn
    collectAllDefns(typeBody) { lkg =>
      lkg.types
        .getOrElse(name, throw new Exception(s"${lkg.self} should contain an type definition for $name by construction"))
        .typeBody
    } { r => r.fields } (Map.empty) { _ ++ _ }
  }

  def wf(t: Type): Boolean = t match {
    case N => true
    case B => true
    case FamType(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      lkg.types.contains(name) || lkg.adts.contains(name)
    case FunType(t1, t2) => wf(t1) && wf(t2)
    case RecType(m) => m.forall { case (_, t) => wf(t) }
    case _ => false
  }

  // TODO: proper subtype check
  def isSubtype(t1: Type, t2: Type): Boolean = t1 == t2

  // TODO: where do we check whether a self path is valid / has meaning?
  //   ie: reject Family X { Family Y { val f: self(Z) -> B = ... } } even if Family Z exists
  // TODO: Boolean or some Result type?
  def typeCheckLinkage(l: Linkage): Boolean =
    //l.defaults.values.forall(typeCheckDefaults(l))
    l.funs.values.forall(typeCheckFunDefns) &&
      l.depot.values.forall(typeCheckCasesDefns) &&
      l.nested.values.forall(typeCheckLinkage)

  // TODO: Do these need current family path?
  def typeCheckFunDefns(f: FunDefn): Boolean = ???

  def typeCheckCasesDefns(c: CasesDefn): Boolean = ???

  // Exceptions or Option?
  def typeOfExpression(G: Map[String, Type])(e: Expression): Type = e match {
    // _________________ T_Num
    // K, G |- n : N
    case Nexp(n) => N

    // _________________ T_Bool
    // K, G |- b : B
    case Bexp(b) => B

    // x: T \in G
    // ________________T_Var
    // K, G |- x : T
    case Var(x) => G.getOrElse(x, throw new Exception(s"Variable $x unbound"))

    // K |- WF(T)
    // K, (x : T, G) |- body : T'
    // _____________________________________ T_Lam
    // K, G |- lam (x : T). body : T -> T'
    case Lam(Var(x), xType, body) =>
      if wf(xType) then {
        FunType(xType, typeOfExpression(G + (x -> xType))(body))
      } else {
        throw new Exception(s"Type $xType is not well-formed")
      }

    // K, G |- e : T
    // K, G |- g : T -> T'
    // _____________________ T_App
    // K, G |- g e : T'
    case App(e1, e2) =>
      typeOfExpression(G)(e1) match { // type e1
        case FunType(iType, oType) =>
          val e2Type = typeOfExpression(G)(e2)
          // TODO: same type or subtype?
          if isSubtype(e2Type, iType) then
            oType
          else
            throw new Exception("TODO bad App rhs incompatible type")
        case _ => throw new Exception("TODO bad App lhs not function type")
      }

    // forall i,
    //     K, G |- e_i : T_i
    // ________________________________________ T_Rec
    // K, G |- {(f_i = e_i)*} : {(f_i: T_i)*}
    case Rec(fields) =>
      val ftypes = fields.map { case (fname, fex) => (fname, typeOfExpression(G)(fex)) }; // type all expressions
      RecType(ftypes)

    // K, G |- e : {(f': T')*}
    // (f: T) in (f': T')*
    // _________________________ T_Proj
    // K, G |- e.f : T
    case Proj(e, f) =>
      typeOfExpression(G)(e) match {
        case RecType(fTypes) => fTypes.getOrElse(f, throw new Exception("TODO no such field"))
        // if we have an instance of a type, the inferred type will be a famtype
        case FamType(Some(p), typeName) =>
          val lkg = getCompleteLinkage(p)
          val typeDefn = lkg.types.getOrElse(typeName, throw new Exception("TODO no such named type"))
          val allTypeFields: Map[String, Type] = collectAllNamedTypeFields(typeDefn)
          allTypeFields.getOrElse(f, throw new Exception("TODO no such field"))
        case _ => throw new Exception("TODO invalid projection")
      }

    // K |- a ~> L
    // m : (T -> T') = lam (x : T). body in L.FUNS
    // _______________________________________________ T_FamFun
    // K, G |- a.m : T -> T'
    case FamFun(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      val FunDefn(_, fType, _) = lkg.funs.getOrElse(name, throw new Exception("TODO no such function"))
      fType

    // K |- a ~> L
    // r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*} =
    //         lam (x: {(f_i:T_i)*}). body in L.CASES
    // _______________________________________________________________ T_Cases
    // K, G |- a.r : {(f_i:T_i)*} -> {(C_j':T_j'->T_j'')*}
    case FamCases(Some(path), name) =>
      val lkg = getCompleteLinkage(path)
      // Validity of type for the defined `cases` will be checked at the top level (ie, match type works with defnType)
      lkg.depot.getOrElse(name, throw new Exception("TODO no such cases")).t

    // K |- a ~> L
    // R = {(f_i: T_i)*} in L.TYPES
    // forall i,
    //     K, G |- e_i : T_i
    // ______________________________________ T_Constructor
    // K, G |- a.R({(f_i = e_i)*}) : a.R
    case Inst(famType@FamType(Some(path), typeName), rec) =>
      val lkg = getCompleteLinkage(path)
      val typeDefn = lkg.types.getOrElse(typeName, throw new Exception(s"No type $typeName in $path"))
      val allTypeFields: Map[String, Type] = collectAllNamedTypeFields(typeDefn)

      if rec.fields.forall { (f, e) => // typeCheck all fields wrt linkage definition
        val fieldType = allTypeFields.getOrElse(f, throw new Exception("TODO no such field"))
        val eType = typeOfExpression(G)(e)
        isSubtype(eType, fieldType)
      } then famType else throw new Exception("TODO field types in instance don't match")

    //  R = \overline{C' {(f': T')*}} in {{a}}
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(famType@FamType(Some(path), tName), cname, rec) =>
      val instFields = rec.fields.view.mapValues(typeOfExpression(G)).toMap
      val lkg = getCompleteLinkage(path)
      val adtDefn = lkg.adts.getOrElse(tName, throw new Exception(s"No ADT $tName in $path"))
      val allCtors: Map[String, RecType] = collectAllConstructors(adtDefn)

      allCtors.getOrElse(cname, throw new Exception(s"No constructor $cname for $tName in $path")) match {
        case RecType(ctorFields) =>
          // we do not allow subtyping within ADT records right now
          if instFields == ctorFields then famType
          else throw new Exception(s"Mismatching field types in ADT instance $cname for $tName in $path")
      }

    // K |- a ~> L
    // K, G |- e : a.R
    // R = \overline{C_i {(f_i: T_i)*}} in L.ADTS
    // g = a'.r {(f_arg = e_arg)*} TODO: optional record instead?
    // K, G |- g: {(C_i: {(f_i: T_i)*} -> T')*}
    // ___________________________________________ T_Match
    // K, G |- match e with g : T'
    case Match(e, g) =>
      typeOfExpression(G)(e) match {
        case FamType(Some(path), tName) =>
          val lkg = getCompleteLinkage(path)
          // look up the name of the ADT type in the linkage
          lkg.adts.getOrElse(tName, throw new Exception("TODO no such ADT")) match {
            case AdtDefn(name, marker, DefnBody(Some(ctors), _, _)) =>
              // TODO: handle when marker == PlusEq... lookup?

              // Checking shape of g
              g match {
                case FamCases(_, _) => ()
                case App(FamCases(_, _), Rec(_)) => ()
                case _ => throw new Exception("TODO invalid match handler")
              }

              typeOfExpression(G)(g) match {
                case RecType(caseFns) if caseFns.size == ctors.size =>
                  // Check that constructor names and fields match,
                  // and that the output types for each handler in the record is consistent
                  // TODO: should this be done at the top-level? cases definition might an extension of the one
                  //       in the family that `e` was defined in
                  caseFns.zip(ctors).toList.foldLeft(Option.empty[Type]) {
                    case (resultType, ((caseCtorName, FunType(inType, outType)), (ctorName, ctorRec)))
                      if caseCtorName == ctorName &&
                        inType == ctorRec &&
                        (resultType.isEmpty || resultType.contains(outType)) =>
                      Some(outType)
                    case _ => throw new Exception("TODO invalid match handler")
                  } match {
                    case None => throw new Exception("Should not be possible for an ADT to have no constructors")
                    case Some(resultType) => resultType
                  }

                case _ => throw new Exception("TODO invalid match handler")
              }
            case _ => throw new Exception("TODO cannot have cases in family that does not extend adt")
          }
        case _ => throw new Exception("TODO invalid expression matched on")
      }

    // All other cases
    case _ => throw new Exception("TODO bad expression")
  }

  // Transforms all self paths into absolute paths (except Prog)
  // TODO: is this what we want?
  def resolvePath(p: Path): Path = p match {
    case Sp(Prog) => p
    case Sp(SelfFamily(pref, fam)) => AbsoluteFamily(resolvePath(Sp(pref)), fam)
    case AbsoluteFamily(pref, fam) => AbsoluteFamily(resolvePath(pref), fam)
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
  def subSelf(newSelf: SelfPath, oldSelf: SelfPath, lkg: Linkage): Linkage = Linkage(
    lkg.path,
    if lkg.self == oldSelf then newSelf else lkg.self,
    lkg.sup,
    lkg.types.view
      .mapValues {
        case TypeDefn(name, marker, typeBody) => TypeDefn(
          name,
          marker,
          subSelfInDefnBody(newSelf, oldSelf, typeBody)(subSelfInType(_, _, _).asInstanceOf[RecType])
        )
      }
      .toMap,
    lkg.defaults.view
      .mapValues {
        case (marker, rec) => marker -> subSelfInExpression(newSelf, oldSelf, rec).asInstanceOf[Rec]
      }
      .toMap,
    lkg.adts.view
      .mapValues {
        case AdtDefn(name, marker, adtBody) => AdtDefn(
          name,
          marker,
          subSelfInDefnBody(newSelf, oldSelf, adtBody) { (ns, os, body) =>
            body.view.mapValues(subSelfInType(ns, os, _).asInstanceOf[RecType]).toMap
          }
        )
      }
      .toMap,
    lkg.funs.view
      .mapValues {
        case FunDefn(name, t, body) => FunDefn(
          name,
          subSelfInType(newSelf, oldSelf, t).asInstanceOf[FunType],
          subSelfInDefnBody(newSelf, oldSelf, body)(subSelfInExpression)
        )
      }
      .toMap,
    lkg.depot.view
      .mapValues {
        case CasesDefn(name, matchType, t, marker, body) => CasesDefn(
          name,
          subSelfInType(newSelf, oldSelf, matchType).asInstanceOf[FamType],
          subSelfInType(newSelf, oldSelf, t).asInstanceOf[FunType],
          marker,
          subSelfInDefnBody(newSelf, oldSelf, body)(subSelfInExpression)
        )
      }
      .toMap,
    lkg.nested.view.mapValues(subSelf(newSelf, oldSelf, _)).toMap
  )
  def subSelfInType(newSelf: SelfPath, oldSelf: SelfPath, t: Type): Type = t match {
    case FamType(path, name) => FamType(path.map(subSelfInPath(newSelf, oldSelf, _)), name)
    case FunType(inType, outType) => FunType(subSelfInType(newSelf, oldSelf, inType), subSelfInType(newSelf, oldSelf, outType))
    case RecType(fields) => RecType(fields.view.mapValues(subSelfInType(newSelf, oldSelf, _)).toMap)
    case _ => t
  }
  def subSelfInExpression(newSelf: SelfPath, oldSelf: SelfPath, e: Expression): Expression = e match {
    case Lam(v, t, body) => Lam(v, subSelfInType(newSelf, oldSelf, t), subSelfInExpression(newSelf, oldSelf, body))
    case FamFun(path, name) => FamFun(path.map(subSelfInPath(newSelf, oldSelf, _)), name)
    case FamCases(path, name) => FamCases(path.map(subSelfInPath(newSelf, oldSelf, _)), name)
    case App(e1, e2) => App(subSelfInExpression(newSelf, oldSelf, e1), subSelfInExpression(newSelf, oldSelf, e2))
    case Rec(fields) => Rec(fields.view.mapValues(subSelfInExpression(newSelf, oldSelf, _)).toMap)
    case Proj(e, name) => Proj(subSelfInExpression(newSelf, oldSelf, e), name)
    case Inst(t, rec) => Inst(
      subSelfInType(newSelf, oldSelf, t).asInstanceOf[FamType],
      subSelfInExpression(newSelf, oldSelf, rec).asInstanceOf[Rec]
    )
    case InstADT(t, cname, rec) => InstADT(
      subSelfInType(newSelf, oldSelf, t).asInstanceOf[FamType],
      cname,
      subSelfInExpression(newSelf, oldSelf, rec).asInstanceOf[Rec]
    )
    case Match(e, g) => Match(subSelfInExpression(newSelf, oldSelf, e), subSelfInExpression(newSelf, oldSelf, g))
    case _ => e
  }
  def subSelfInDefnBody[B](newSelf: SelfPath, oldSelf: SelfPath, body: DefnBody[B])(subB: (SelfPath, SelfPath, B) => B): DefnBody[B] =
    DefnBody(
      body.defn.map(subB(newSelf, oldSelf, _)),
      body.extendsFrom.map(subSelfInPath(newSelf, oldSelf, _)),
      body.furtherBindsFrom.map(subSelfInPath(newSelf, oldSelf, _))
    )
  def subSelfInPath(newSelf: SelfPath, oldSelf: SelfPath, p: Path): Path = p match {
    case Sp(sp) if sp == oldSelf => Sp(newSelf)
    case _ => p
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
      val l1SelfSubbed = subSelf(l2.self, l1.self, markInheritForm(l1InheritForm, l1))
      Linkage(
        l2.path,
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
    case (FunDefn(funF, fType, _), overridingFunDefn@FunDefn(_funF, fTypePrime, _))
      if fType == fTypePrime => overridingFunDefn
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
    // TODO: check type names of prevMatchType and curMatchType are the same? (without paths)
    case ( CasesDefn(casesName, prevMatchType, prevT, _, prevCasesDefn)
         , CasesDefn(_casesName, curMatchType, curT, PlusEq, curCasesDefn)
         ) =>
      val resultT: Type = (prevT, curT) match {
        case (RecType(_), RecType(_)) => curT
        case (FunType(RecType(prevFields), RecType(_)), FunType(RecType(curFields), curOutT@RecType(_))) =>
          // TODO: or should we check curInT is subtype of prevInT?
          FunType(RecType(prevFields ++ curFields), curOutT)
        case _ => throw new Exception("TODO invalid cases definition")
      }
      // For implementation purposes, we do not absorb inherited cases directly.
      // The result `DefnBody` is instead marked with information about where it inherits from,
      // which is used to look up those other cases recursively
      CasesDefn(casesName, curMatchType, resultT, PlusEq, curCasesDefn)
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
  def concatNested(nested1: Map[String, Linkage], nested2: Map[String, Linkage]): Map[String, Linkage] = {
    unionWith(nested1, nested2) { (lkgLPrime_A, lkgI_A) =>
      val lkgL: Linkage = getCompleteLinkage(Sp(lkgLPrime_A.self))
      concatLinkages(FurtherBinds)(Some(lkgL), lkgI_A)
    }
  }
}
