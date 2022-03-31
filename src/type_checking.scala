import famfun._

object type_checking {
  val K: scala.collection.mutable.Map[Path, Linkage] = scala.collection.mutable.Map.empty

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

  def isSubtype(t1: Type, t2: Type): Boolean = ???

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
          val (marker, RecType(fields)) = lkg.types.getOrElse(typeName, throw new Exception("TODO no such named type"))
          fields.getOrElse(f, throw new Exception("TODO no such field"))
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
      val CasesDefn(_, _, defnType, _, _) = lkg.depot.getOrElse(name, throw new Exception("TODO no such cases"))
      defnType

    // K |- a ~> L
    // R = {(f_i: T_i)*} in L.TYPES
    // forall i,
    //     K, G |- e_i : T_i
    // ______________________________________ T_Constructor
    // K, G |- a.R({(f_i = e_i)*}) : a.R
    case Inst(famType@FamType(Some(path), typeName), rec) =>
      val lkg = getCompleteLinkage(path)
      val (marker, recType) = lkg.types.getOrElse(typeName, throw new Exception("TODO no such type"))
      // TODO: get all fields if extended (marker == PlusEq)
      if rec.fields.forall { (f, e) => // typeCheck all fields wrt linkage definition
        val fieldType = recType.fields.getOrElse(f, throw new Exception("TODO no such field"))
        val eType = typeOfExpression(G)(e)
        isSubtype(eType, fieldType)
      } then famType else throw new Exception("TODO field types in instance don't match")

    //  R = \overline{C' {(f': T')*}} in {{a}}
    //  C {(f_i: T_i)*} in \overline{C' {(f': T')*}}
    //  forall i, G |- e_i : T_i
    //_________________________________________________ T_ADT
    //  G |- a.R(C {(f_i = e_i)*}) : a.R
    case InstADT(famType@FamType(Some(path), tName), cname, rec) =>
      val ctorFields = rec.fields.view.mapValues(typeOfExpression(G)).toMap
      val lkg = getCompleteLinkage(path)
      val ADT(name, marker, cs) = lkg.adts.getOrElse(tName, throw new Exception("TODO no such ADT"))
      // TODO: get all ctors if extended (marker == PlusEq)
      cs.getOrElse(cname, throw new Exception("No such constructor")) match {
        case RecType(instFields) =>
          // we do not allow subtyping within ADT records right now
          if instFields == ctorFields then famType
          else throw new Exception("TODO field types in ADT instance don't match")
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
          val ADT(name, marker, ctors) = lkg.adts.getOrElse(tName, throw new Exception("TODO no such ADT"))
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
      val incompleteCurLkg = enclosingLkg.nested.getOrElse(fam, throw new Exception("TODO no such path"))
      // L'
      val optSupLkg = incompleteCurLkg.sup.map(getCompleteLinkage)

      concatLinkages(optSupLkg, incompleteCurLkg)
  }


  // Recursively substitutes instances of `newSelf` for `oldSelf` in lkg
  // lkg [newSelf / oldSelf]
  def subSelf(newSelf: SelfPath, oldSelf: SelfPath, lkg: Linkage): Linkage = Linkage(
    lkg.path,
    if lkg.self == oldSelf then newSelf else lkg.self,
    lkg.sup,
    lkg.types.view
      .mapValues {
        case (marker, recType) => marker -> subSelfInType(newSelf, oldSelf, recType).asInstanceOf[RecType]
      }
      .toMap,
    lkg.defaults.view
      .mapValues {
        case (marker, rec) => marker -> subSelfInExpression(newSelf, oldSelf, rec).asInstanceOf[Rec]
      }
      .toMap,
    lkg.adts.view
      .mapValues {
        case ADT(name, marker, cs) => ADT(
          name,
          marker,
          cs.view.mapValues(subSelfInType(newSelf, oldSelf, _).asInstanceOf[RecType]).toMap
        )
      }
      .toMap,
    lkg.funs.view
      .mapValues {
        case FunDefn(name, t, body) => FunDefn(
          name,
          subSelfInType(newSelf, oldSelf, t).asInstanceOf[FunType],
          subSelfInDefnBody(newSelf, oldSelf, body)
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
          subSelfInDefnBody(newSelf, oldSelf, body)
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
  def subSelfInDefnBody(newSelf: SelfPath, oldSelf: SelfPath, body: DefnBody): DefnBody = body match {
    case BodyDeclared(defined) => BodyDeclared(subSelfInExpression(newSelf, oldSelf, defined))
    // TODO: is this needed/right?
    case BodyInherited(from) => BodyInherited(subSelfInPath(newSelf, oldSelf, from))
  }
  def subSelfInPath(newSelf: SelfPath, oldSelf: SelfPath, p: Path): Path = p match {
    case Sp(sp) if sp == oldSelf => Sp(newSelf)
    case _ => p
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
  def concatLinkages(optL1: Option[Linkage], l2: Linkage): Linkage = optL1 match {
    case None => l2
    case Some(l1) =>
      val l1SelfSubbed = subSelf(l2.self, l1.self, l1)
      Linkage(
        l2.path,
        l2.self,
        l2.sup,
        concatTypes(l1SelfSubbed.types, l2.types),
        concatDefaults(l1SelfSubbed.defaults, l2.defaults),
        concatAdts(l1SelfSubbed.adts, l2.adts),
        concatFuns(l1SelfSubbed.funs, l2.funs),
        concatCases(l1SelfSubbed.depot, l2.depot),
        concatNested(l1SelfSubbed.nested, l2.nested)
      )
  }

  def concatTypes(types1: Map[String, (Marker, RecType)], types2: Map[String, (Marker, RecType)]): Map[String, (Marker, RecType)] = ???

  def concatDefaults(defaults1: Map[String, (Marker, Rec)], defaults2: Map[String, (Marker, Rec)]): Map[String, (Marker, Rec)] = ???

  def concatAdts(adts1: Map[String, ADT], adts2: Map[String, ADT]): Map[String, ADT] = ???

  def concatFuns(funs1: Map[String, FunDefn], funs2: Map[String, FunDefn]): Map[String, FunDefn] = ???

  def concatCases(depot1: Map[String, CasesDefn], depot2: Map[String, CasesDefn]): Map[String, CasesDefn] = ???

  def concatNested(nested1: Map[String, Linkage], nested2: Map[String, Linkage]): Map[String, Linkage] = ???
}
