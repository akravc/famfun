import OptionOps.firstSome
import famfun.*
import type_checking.{collectAllCaseHandlerTypes, collectAllDefaults, collectAllDefns, collectAllNamedTypeFields, getCompleteLinkage, unifyTypes}

import reflect.Selectable.reflectiveSelectable

object code_generation {
  val codeCache: scala.collection.mutable.Map[String, String] = scala.collection.mutable.Map.empty

  // Every getCompleteLinkage call should be a Right for the paths we use after type-checking
  def getCompleteLinkageUnsafe(p: Path): Linkage =
    getCompleteLinkage(p).getOrElse(throw new Exception("Should not happen after type-checking"))

  val indent: String = "  "

  def indentBy(n: Int)(str: String): String = indent + str.flatMap {
    case '\n' => s"\n$indent"
    case c => c.toString
  }

  def linkageFileName(lkg: Linkage): String = s"${pathIdentifier(lkg.path)(lkg.path)}.scala"

  def pathIdentifier(curPath: Path)(p: Path): String = {
    p match {
      case Sp(_) => {
        val famList = pathToFamList(p)
        val n = famList.size
        val curFamList = pathToFamList(curPath)
        s"self$$${if (curFamList.size==n) "" else n}"
      }
      case AbsoluteFamily(_, _) => absolutePathIdentifier(p)
    }
  }

  def absolutePathIdentifier(p: Path) =
    pathToFamList(p).mkString("$")

  def selfPathsInScope(p: Path): List[String] =
    prefixPaths(p, Nil)
      .map(absolutePathIdentifier)

  def generateSelfParts(p: Path): List[(String, String)] = {
    val ps = selfPathsInScope(p)
    val n = ps.size
    ps.zipWithIndex.map { (selfParam, i) => (s"self$$${if ((i+1)==n) "" else (i+1)}", selfParam) }
  }
  def generateSelfParams(p: Path): List[String] =
    generateSelfParts(p).map { (self, p) => s"$self: $p.Interface" }

  def findPathAdt(curDefn: AdtDefn, curPath: Path)(check: (Map[String, RecType], Path) => Boolean): List[Path] = {
    def findNext(nextPath: Path): List[Path] = {
      val nextLkg = getCompleteLinkageUnsafe(nextPath)
      val nextDefn =
        nextLkg.adts.getOrElse(curDefn.name, throw new Exception("Should be defined after type-checking"))
      findPathAdt(nextDefn, nextPath)(check)
    }

    def resultIfNonNil(restResult: List[Path]): List[Path] = restResult match {
      case Nil => Nil
      case _ => curPath :: restResult
    }

    curDefn.adtBody match {
      case DefnBody(Some(curCtors), _, _, _) if check(curCtors, curPath) => List(curPath)
      case DefnBody(_, None, None, _) => Nil
      case DefnBody(_, None, Some(furtherBindsFrom), _) => resultIfNonNil(findNext(furtherBindsFrom))
      case DefnBody(_, Some(extendsFrom), None, _) => resultIfNonNil(findNext(extendsFrom))
      case DefnBody(_, Some(extendsFrom), Some(furtherBindsFrom), _) => resultIfNonNil(findNext(furtherBindsFrom)) match {
        case Nil => resultIfNonNil(findNext(extendsFrom))
        case result => result
      }
    }
  }

  // Finds a path of paths to a constructor from the current adt defn
  def findPathToConstructor(curDefn: AdtDefn, curPath: Path, ctorName: String): List[Path] = {
    findPathAdt(curDefn, curPath) { (ctors, _) => ctors.contains(ctorName) }
  }

  // Finds a  path of paths to a path containing the currently extended adt type from the current adt defn
  def findPathToPath(curDefn: AdtDefn, curPath: Path, targetPath: Path): List[Path] = {
    findPathAdt(curDefn, curPath) { (_, p) => p == targetPath }
  }

  // Produces the path of the family that the family of the given path further binds from
  def findFurtherBinds(path: Path): Option[Path] = {
    def findNext(optNextPath: Option[Path], targetFam: String): Option[Path] = for {
      nextPath <- optNextPath
      nextLkg = getCompleteLinkageUnsafe(nextPath)
      resultLkg <- nextLkg.nested.get(targetFam)
    } yield resultLkg.path

    path match {
      case Sp(Prog) => None
      case Sp(_) => findFurtherBinds(concretizePath(path))
      case AbsoluteFamily(pref, fam) =>
        val prefLkg: Linkage = getCompleteLinkageUnsafe(pref)
        val fromExtends: Option[Path] = findNext(prefLkg.sup, fam)
        lazy val fromFurtherBinds: Option[Path] = findNext(findFurtherBinds(prefLkg.path), fam)
        firstSome(fromExtends, fromFurtherBinds)
    }
  }

  def sentinelPathIdentifier(p: Path): String = p match {
    case Sp(sp) => sentinelSelfPathIdentifier(sp)
    case AbsoluteFamily(Sp(Prog), fam) => fam
    case AbsoluteFamily(Sp(pref), fam) => sentinelSelfPathIdentifier(pref) + "$" + fam
    case AbsoluteFamily(pref, fam) => sentinelPathIdentifier(pref) + "$$" + fam
  }

  def sentinelSelfPathIdentifier(sp: SelfPath): String = sp match {
    case Prog => ""
    case SelfFamily(Sp(Prog), fam) => fam
    case SelfFamily(Sp(pref), fam) => sentinelSelfPathIdentifier(pref) + "$" + fam
    case SelfFamily(pref, fam) => sentinelPathIdentifier(pref) + "$$" + fam
  }

  def isSentinelPath(p: Path): Boolean = p match {
    case Sp(sp) => isSentinelSelfPath(sp)
    case AbsoluteFamily(Sp(Prog), fam) => false
    case AbsoluteFamily(Sp(pref), fam) => true
    case AbsoluteFamily(pref, fam) => isSentinelPath(pref)
  }

  def isSentinelSelfPath(sp: SelfPath): Boolean = sp match {
    case Prog => false
    case SelfFamily(Sp(Prog), fam) => false
    case SelfFamily(Sp(pref), fam) => true
    case SelfFamily(pref, fam) => isSentinelPath(pref)
  }

  def prefixPaths(p: Path, acc: List[Path]): List[Path] = p match {
    case Sp(sp) => prefixSelfPaths(sp, acc)
    case AbsoluteFamily(pref, fam) => prefixPaths(pref, p::acc)
  }

  def prefixSelfPaths(p: SelfPath, acc: List[Path]): List[Path] = p match {
    case Prog => acc
    case SelfFamily(pref, fam) => prefixPaths(pref, Sp(p)::acc)
  }

  def conflictPaths(p: Path): List[Path] =
    prefixPaths(Sp(relativizePath(p)), Nil).reverse.tail.reverse

  def hasConflictingSelfs(curPath: Path, supPath: Path): Boolean =
    !conflictPaths(curPath)
      .zip(conflictPaths(supPath))
      .map{_ == _}
      .forall{(b: Boolean) => b}

  def ensureLinkage(curPath: Path)(p: Path): Unit = {
    if (hasConflictingSelfs(curPath, p)) {
      val fn = sentinelPathIdentifier(p)+".scala"
      codeCache.get(fn) match {
        case None => {
          codeCacheLinkage(fn, generateSentinelCode(p))
        }
        case Some(_) =>
      }
     }
  }

  def codeCacheLinkage(fn: String, gen: => String): Unit = {
    codeCache.get(fn) match {
      case Some(_) =>
      case None => {
        codeCache(fn) = "// TODO"
        println(s"generating $fn...")
        codeCache(fn) = gen
      }
    }
  }

  // Produces a list of pairs of desired file names with the code they contain
  // generated from the complete linkages given
  def generateCode(completeLinkages: Iterable[Linkage]): Iterable[(String, String)] = {
    codeCache.clear()
    completeLinkages
      .filter { _.self != Prog }
      .foreach { lkg =>
        codeCacheLinkage(linkageFileName(lkg), generateCodeLinkage(lkg))
      }
    codeCache
  }

  def generateSentinelCode(p: Path): String = {
    val lkg = getCompleteLinkageUnsafe(p)

    val typesCode: String = lkg.types.values.map(generateSentinelCodeTypeDefn(p)).mkString("\n")

    val adtsCode: String = lkg.adts.values.map(generateSentinelCodeAdtDefn(p)).mkString("\n")

    val interfaceCode: String = generateSentinelCodeInterface(p)(lkg.types.values, lkg.adts.values, lkg.funs.values, lkg.depot.values)
    val familyCode: String = generateSentinelCodeFamily(p, lkg.sup)(lkg.types.values, lkg.adts.values, lkg.funs.values, lkg.depot.values)

    s"""import reflect.Selectable.reflectiveSelectable
       |
       |object ${sentinelPathIdentifier(p)} {
       |  // Types
       |${indentBy(1)(typesCode)}
       |
       |  // ADTs
       |${indentBy(1)(adtsCode)}
       |
       |  // Path interface
       |${indentBy(1)(interfaceCode)}
       |
       |  // Path implementation
       |${indentBy(1)(familyCode)}
       |}""".stripMargin

  }

  def generateCodeLinkage(lkg: Linkage): String = {
    val typesCode: String = lkg.types.values.map(generateCodeTypeDefn(lkg.path)).mkString("\n")

    val adtsCode: String = lkg.adts.values.map(generateCodeAdtDefn(lkg.path)).mkString("\n")

    val interfaceCode: String = generateCodeInterface(lkg.path)(lkg.types.values, lkg.adts.values, lkg.funs.values, lkg.depot.values)
    val familyCode: String = generateCodeFamily(lkg.path, lkg.sup)(lkg.types.values, lkg.adts.values, lkg.funs.values, lkg.depot.values)

    s"""import reflect.Selectable.reflectiveSelectable
       |
       |object ${pathIdentifier(lkg.path)(lkg.path)} {
       |  // Types
       |${indentBy(1)(typesCode)}
       |
       |  // ADTs
       |${indentBy(1)(adtsCode)}
       |
       |  // Path interface
       |${indentBy(1)(interfaceCode)}
       |
       |  // Path implementation
       |${indentBy(1)(familyCode)}
       |}""".stripMargin
  }

  def generateSentinelCodeInterface(curPath: Path)
                                   (types: Iterable[TypeDefn], adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    generateCodeInterface(curPath)(types, adts, funs, cases)
  }

  def generateCodeInterface(curPath: Path)
                           (types: Iterable[TypeDefn], adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    val curPathId: String = pathIdentifier(curPath)(curPath)

    val allBodies: Iterable[DefnBody[Expression]] = funs.map { _.funBody } ++ cases.map { _.casesBody }

    val extensionPaths: List[Path] = (getCompleteLinkageUnsafe(curPath).sup, findFurtherBinds(curPath)) match {
      case (None, None) => List()
      case (Some(extendsPath), None) => List(extendsPath)
      case (None, Some(furtherBindsPath)) => List(furtherBindsPath)
      case (Some(extendsPath), Some(furtherBindsPath)) => List(extendsPath, furtherBindsPath)
    }

    extensionPaths.foreach(ensureLinkage(curPath))

    val interfaceExtension: String = extensionPaths.map{p => s"${pathIdentifier(curPath)(p)}.Interface"} match {
      case Nil => ""
      case List(a) => s"extends $a"
      case List(a, b) => s"extends $a with $b"
    }

    val selfFields: String = generateSelfParams(curPath).map { selfWithType =>
      s"val $selfWithType"
    }.mkString("\n")

    val selfTypesSig: String = types.map(typeDefn => s"type ${typeDefn.name}").mkString("\n")

    val selfAdtsSig: String = adts.map(adtDefn => s"type ${adtDefn.name}").mkString("\n")

    val funsSig: String = funs.map(generateCodeFunSignature(curPath)(None)).mkString("\n")

    val casesSig: String = cases.map(generateCodeCasesSignature(curPath)).mkString("\n")

    val translationsSig: String = adts.map { adtDefn =>
      val adtName: String = adtDefn.name
      s"def $curPathId$$$$$adtName(from: $curPathId.$adtName): $adtName"
    }.mkString("\n")

    s"""trait Interface $interfaceExtension {
       |  // Self fields
       |${indentBy(1)(selfFields)}
       |
       |  // Self Named types
       |${indentBy(1)(selfTypesSig)}
       |
       |  // Self ADTs
       |${indentBy(1)(selfAdtsSig)}
       |
       |  // Functions
       |${indentBy(1)(funsSig)}
       |
       |  // Cases
       |${indentBy(1)(casesSig)}
       |
       |  // Translations
       |${indentBy(1)(translationsSig)}
       |}""".stripMargin
  }

  def generateSentinelCodeFamily(curPath: Path, supPath: Option[Path])
                        (types: Iterable[TypeDefn], adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    s"// TODO"
  }

  def generateCodeFamily(curPath: Path, supPath: Option[Path])
                        (types: Iterable[TypeDefn], adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    val curPathId: String = pathIdentifier(curPath)(curPath)

    val selfFields: String = {
      val parts = generateSelfParts(curPath)
      var s = parts
        .map { (self, p) => s"override val $self: $p.Interface = $p.Family"}
        .mkString("\n")
      // TODO(now): this is a hack!
      supPath.foreach{ supPath =>
        val n = parts.size
        val supParts = selfPathsInScope(supPath)
        val sn = supParts.size
        if (n < sn) {
          s = s + "\n" + supParts.drop(n-1).take(sn-n).zipWithIndex.map{ (p, i) => s"override val self$$${i+n}: $p.Interface = $p.Family" }.mkString("\n")
        }
      }
      s
    }


    val typesCode: String = types.map { typeDefn =>
      s"override type ${typeDefn.name} = ${pathIdentifier(curPath)(curPath)}.${typeDefn.name}"
    }.mkString("\n")

    val adtsCode: String = adts.map { adtDefn =>
      s"override type ${adtDefn.name} = ${pathIdentifier(curPath)(curPath)}.${adtDefn.name}"
    }.mkString("\n")

    val funsCode: String = funs.map(generateCodeFunDefn(curPath)).mkString("\n")

    val casesCode: String = cases.map(generateCodeCasesDefn(curPath)).mkString("\n")

    val translationsCode: String = adts.map(generateCodeTranslationFunction(curPath)).mkString("\n")

    s"""object Family extends ${pathIdentifier(curPath)(curPath)}.Interface {
       |  // Self field instantiation
       |${indentBy(1)(selfFields)}
       |
       |  // Self named types instantiation
       |${indentBy(1)(typesCode)}
       |
       |  // Self ADTs instantiation
       |${indentBy(1)(adtsCode)}
       |
       |  // Function implementations
       |${indentBy(1)(funsCode)}
       |
       |  // Cases implementations
       |${indentBy(1)(casesCode)}
       |
       |  // Translation function implementations
       |${indentBy(1)(translationsCode)}
       |}""".stripMargin
  }

  def generateSentinelCodeTypeDefn(curPath: Path)(typeDefn: TypeDefn): String = {
    s"// TODO"
  }

  def generateCodeTypeDefn(curPath: Path)(typeDefn: TypeDefn): String = {
    val allFields: Map[String, Type] = collectAllNamedTypeFields(typeDefn).getOrElse(throw new Exception("Shouldn't happen"))

    s"type ${typeDefn.name} = ${generateCodeType(curPath)(RecType(allFields))}"
  }

  def generateSentinelCodeAdtDefn(curPath: Path)(adtDefn: AdtDefn): String = {
    s"// TODO"
  }

  def generateCodeAdtDefn(curPath: Path)(adtDefn: AdtDefn): String = {
    val adtName: String = adtDefn.name

    val definedCtors: List[String] = adtDefn.adtBody.defn match {
      case None => Nil
      case Some(ctors) =>
        ctors.toList.map {
          case (ctorName, RecType(ctorFields)) =>
            val typeParams: scala.collection.mutable.Set[String] = scala.collection.mutable.Set.empty
            val caseClassFields =
              ctorFields
                .map { (fieldName, fieldType) =>
                  val fieldTypeCode = fieldType match {
                    case FamType(Some(p@Sp(_)), name) if getCompleteLinkageUnsafe(p).adts.contains(name) =>
                      val famTypeCode = s"${pathIdentifier(curPath)(p)}$$$$$name"
                      typeParams += famTypeCode
                      famTypeCode
                    case _ => generateCodeType(curPath)(fieldType)
                  }
                  s"$fieldName: $fieldTypeCode"
                }
                .mkString(", ")
            val typeParamsCode: String = if typeParams.isEmpty then "" else s"[${typeParams.mkString(", ")}]"
            s"case class $ctorName$typeParamsCode($caseClassFields) extends $adtName"
        }
    }
    val inheritCtors: List[String] =
      List(adtDefn.adtBody.extendsFrom, adtDefn.adtBody.furtherBindsFrom)
        .collect { case Some(inheritPath) =>
          val inheritPathCode = pathIdentifier(curPath)(inheritPath)
          s"""case class $inheritPathCode$$$$$adtName(inherited: $inheritPathCode.$adtName) extends $adtName {
             |  override def toString(): String = inherited.toString()
             |}""".stripMargin
        }

    s"""sealed trait $adtName
       |// Defined constructors
       |${definedCtors.mkString("\n")}
       |// Inherited constructors
       |${inheritCtors.mkString("\n")}
       |""".stripMargin
  }

  def generateSelfArgs(curPath: Path)(parentPath: Path): String = {
    val n = pathToFamList(parentPath).size
    (1 to n).map { i => s"self$$${if (i==n) "" else i}" }.mkString(", ")
  }

  def generateSentinelCodeFunDefn(curPath: Path)(funDefn: FunDefn): String = {
    s"// TODO"
  }

  def generateCodeFunDefn(curPath: Path)(funDefn: FunDefn): String = {
    val implBody: String = funDefn.funBody match {
      case DefnBody(None, _, Some(furtherBindsPath), _) =>
        s"${pathIdentifier(curPath)(furtherBindsPath)}.Family.${funDefn.name}$$Impl(${generateSelfArgs(curPath)(furtherBindsPath)})"
      case DefnBody(None, Some(extendsPath), None, _) =>
        s"${pathIdentifier(curPath)(extendsPath)}.Family.${funDefn.name}$$Impl(${generateSelfArgs(curPath)(extendsPath)})"
      case DefnBody(Some(expr), _, _, _) =>
        generateCodeExpression(curPath)(expr)
    }

    s"""override ${generateCodeFunSignature(curPath)(None)(funDefn)} = ${funDefn.name}$$Impl(${generateSelfArgs(curPath)(curPath)})
       |${generateCodeFunSignature(curPath)(Some(curPath))(funDefn)} =
       |${indentBy(1)(implBody)}""".stripMargin
  }

  // When optSelf is Some(_), generates the signature for the $Impl function
  def generateCodeFunSignature(curPath: Path)(optPath: Option[Path])(funDefn: FunDefn): String = optPath match {
    case None => s"val ${funDefn.name}: ${generateCodeType(curPath)(funDefn.t)}"
    case Some(curPath) =>
      val selfParamsCode: String = generateSelfParams(curPath).mkString(", ")
      s"def ${funDefn.name}$$Impl($selfParamsCode): ${generateCodeType(curPath)(funDefn.t)}"
  }

  def generateCodeCasesDefn(curPath: Path)(casesDefn: CasesDefn): String = {
    val matchType: FamType = casesDefn.matchType
    val concreteMatchTypeCode: String = generateCodeType(curPath)(concretizeType(matchType))
    val matchTypePath: Path = concretizePath(
      matchType.path
        .getOrElse(throw new Exception("Should not have None paths after name resolution"))
    )
    val matchTypePathId: String = pathIdentifier(curPath)(matchTypePath)
    val matchTypePathLkg: Linkage = getCompleteLinkageUnsafe(matchTypePath)
    val matchTypeAdtDefn: AdtDefn =
      matchTypePathLkg.adts.getOrElse(matchType.name, throw new Exception("Should be defined after type-checking"))

    val (envParamName, envParamType, definedClauses): (String, Type, List[String]) = casesDefn.casesBody.defn match {
      case None => casesDefn.t match {
        case FunType(envType, _) => ("env", envType, Nil)
        case _ => throw new Exception("Other types for cases definitions not handled")
      }
      case Some(Lam(Var(v), t, Rec(caseHandlers))) =>
        val clauses = caseHandlers.toList.map {
          case (ctorName, Lam(Var(instName), RecType(ctorFieldTypes), handlerExp)) =>
            val pathToCtor: List[Path] = findPathToConstructor(matchTypeAdtDefn, matchTypePath, ctorName)
            val lastCtorCode: String = s"${pathIdentifier(curPath)(pathToCtor.last)}.$ctorName"
            val ignoredFields = List.fill(ctorFieldTypes.size)("_").mkString(", ")
            val caseMatched: String =
              ctorCallListFromPathList(curPath)(pathToCtor, matchType.name)
                .foldRight(s"matched@$lastCtorCode($ignoredFields)") { (c, r) => s"$c($r)" }

            val typeArgs: Set[String] = ctorFieldTypes.values.toSet.flatMap {
              case FamType(Some(p), name) if getCompleteLinkageUnsafe(p).adts.contains(name) =>
                Set(s"${pathIdentifier(curPath)(p)}.$name")
              case _ => Set.empty
            }
            val typeArgsCode: String = if typeArgs.isEmpty then "" else s"[${typeArgs.mkString(", ")}]"
            val instType: String = s"$lastCtorCode$typeArgsCode"
            val matchedCast: String = if typeArgs.isEmpty then "" else s".asInstanceOf[$instType]"
            s"""case $caseMatched =>
               |  val $instName: $instType = matched$matchedCast
               |  val $instName$$proj = $instName
               |${indentBy(1)(generateCodeExpression(curPath)(handlerExp))}""".stripMargin
          case _ => throw new Exception("Other shapes for case handlers not handled")
        }
        (if v == "_" then "unused$" else v, t, clauses)
      case _ => throw new Exception("Other shapes for cases definitions not handled")
    }

    val inheritedClauses: List[String] =
      List(casesDefn.casesBody.extendsFrom, casesDefn.casesBody.furtherBindsFrom)
        .collect { case Some(inheritPath) =>
          val inheritPathCode = pathIdentifier(curPath)(inheritPath)
          s"""case $matchTypePathId.$inheritPathCode$$$$${matchType.name}(inherited) =>
             |  $inheritPathCode.Family.${casesDefn.name}$$Impl(${generateSelfArgs(curPath)(inheritPath)})(inherited)($envParamName)""".stripMargin
        }

    val caseClauses: List[String] = definedClauses ++ inheritedClauses

    s"""${generateCodeCasesSignature(curPath)(casesDefn)} = ${casesDefn.name}$$Impl(${generateSelfArgs(curPath)(curPath)})(matched.asInstanceOf[$concreteMatchTypeCode])
       |${generateCodeCasesImplSignature(curPath)(casesDefn)} = ($envParamName: ${generateCodeType(curPath)(envParamType)}) => matched match {
       |${indentBy(1)(caseClauses.mkString("\n"))}
       |}""".stripMargin
  }

  def generateCodeCasesSignature(curPath: Path)(casesDefn: CasesDefn): String = {
    val envType: Type = casesDefn.t match {
      case FunType(input, _) => input
      case _ => throw new Exception("Other shapes for cases types not handled")
    }
    val outType: Type = (for {
      allCaseHandlerTypes <- collectAllCaseHandlerTypes(casesDefn)
      caseHandlerOutTypes = allCaseHandlerTypes.values.map {
        case FunType(_, outType) => outType
        case _ => throw new Exception("Should not happen after type-checking")
      }.toList
      outT <- unifyTypes(caseHandlerOutTypes/*.map(subSelfInTypeAccordingTo(curPath))*/)
    } yield outT).getOrElse(throw new Exception("Should not happen after type-checking"))
    val casesDefnType: Type = FunType(envType, outType)

    s"def ${casesDefn.name}(matched: ${generateCodeType(curPath)(casesDefn.matchType)}): ${generateCodeType(curPath)(casesDefnType)}"
  }
  def generateCodeCasesImplSignature(curPath: Path)(casesDefn: CasesDefn): String = {
    val envType: Type = casesDefn.t match {
      case FunType(input, _) => input
      case _ => throw new Exception("Other shapes for cases types not handled")
    }
    val outType: Type = (for {
      allCaseHandlerTypes <- collectAllCaseHandlerTypes(casesDefn)
      caseHandlerOutTypes = allCaseHandlerTypes.values.map {
        case FunType(_, outType) => outType
        case _ => throw new Exception("Should not happen after type-checking")
      }.toList
      outT <- unifyTypes(caseHandlerOutTypes/*.map(subSelfInTypeAccordingTo(curPath))*/)
    } yield outT).getOrElse(throw new Exception("Should not happen after type-checking"))
    val casesDefnType: Type = FunType(envType, outType)

    val concreteMatchType = concretizeType(casesDefn.matchType)
    val selfParamsCode: String = generateSelfParams(curPath).mkString(", ")
    s"def ${casesDefn.name}$$Impl($selfParamsCode)(matched: ${generateCodeType(curPath)(concreteMatchType)}): ${generateCodeType(curPath)(casesDefnType)}"
  }

  def ctorCallListFromPathList(curPath: Path)(pathList: List[Path], adtName: String): List[String] = pathList match {
    case p1 :: p2 :: ps => s"${pathIdentifier(curPath)(p1)}.${pathIdentifier(curPath)(p2)}$$$$$adtName" :: ctorCallListFromPathList(curPath)(p2 :: ps, adtName)
    case _ => Nil
  }

  def generateCodeTranslationFunction(curPath: Path)(adtDefn: AdtDefn): String = {
    val curPathId: String = pathIdentifier(curPath)(curPath)

    // Collect all paths from which this adt extends a definition
    val (inheritedPaths, _) = collectAllDefns(adtDefn)(_.adtBody) { lkg =>
      lkg.adts
        .getOrElse(adtDefn.name, throw new Exception(s"${lkg.self} should contain an ADT definition for ${adtDefn.name} by construction"))
    } { _ => () } (()) { (_, _) => () }.getOrElse(throw new Exception("Should not fail after type-checking"))

    val allPaths = curPath :: inheritedPaths.toList

    allPaths.map { targetPath =>
      val targetPathId: String = pathIdentifier(curPath)(targetPath)
      // TODO: find target paths and generate translation terms at once to be more efficient
      val ctorCalls = ctorCallListFromPathList(curPath)(findPathToPath(adtDefn, curPath, targetPath), adtDefn.name)
      val translationTerm: String = ctorCalls.foldRight("from") { (c, r) =>
        s"$c($r)"
      }
      // TODO(now): commented out because these don't compile?
      val finalTranslationTerm: String =
        if (curPath != targetPath && translationTerm == "from") "???/*TODO*/" else translationTerm

      s"def $targetPathId$$$$${adtDefn.name}(from: $targetPathId.${adtDefn.name}): ${adtDefn.name} = $finalTranslationTerm"
    }.mkString("\n")
  }

  def generateCodeType(curPath: Path)(t: Type): String = t match {
    case NType => "Int"
    case BType => "Boolean"
    case StringType => "String"
    case FamType(Some(p), name) => s"${pathIdentifier(curPath)(p)}.$name"
    case FamType(None, name) => throw new Exception("Should not have None paths after name resolution")
    case FunType(input, output) => s"${generateCodeType(curPath)(input)} => ${generateCodeType(curPath)(output)}"
    case RecType(fields) =>
      if fields.isEmpty then "Unit"
      else {
        val fieldsCode =
          fields
            .map { (fieldName, fieldType) => s"val $fieldName: ${generateCodeType(curPath)(fieldType)}" }
            .mkString("; ")

        s"{$fieldsCode}"
      }
  }

  def generateCodeExpression(curPath: Path)(e: Expression): String = e match {
    case Var(id) => s"$id"

    case Lam(Var(v), t, body) =>
      s"""($v: ${generateCodeType(curPath)(t)}) => {
         |${indentBy(1)(generateCodeExpression(curPath)(body))}
         |}""".stripMargin

    case FamFun(Some(path), name) => path match {
      case AbsoluteFamily(_, _) =>
        val selfArgs: String = selfPathsInScope(path).map(_ ++ ".Family").mkString(", ")
        s"${pathIdentifier(curPath)(path)}.Family.$name$$Impl($selfArgs)"
      case Sp(_) =>
        // TODO: only cast if needed (fType contains relative types)
        val Some(fType) = e.exprType
        s"${pathIdentifier(curPath)(path)}.$name.asInstanceOf[${generateCodeType(curPath)(fType)}]"
    }
    case FamFun(None, _) => throw new Exception("Should not have None paths after name resolution")

    case FamCases(Some(path), name) => path match {
      case AbsoluteFamily(_, _) =>
        val selfArgs: String = selfPathsInScope(path).map(_ ++ ".Family").mkString(", ")
        s"${pathIdentifier(curPath)(path)}.Family.$name$$Impl($selfArgs)"
      case Sp(_) =>
        val lkg: Linkage = getCompleteLinkageUnsafe(path)
        val casesDefn: CasesDefn = lkg.depot.getOrElse(name, throw new Exception("Should exist after type checking"))
        val envType: Type = casesDefn.t match {
          case FunType(input, _) => input
          case _ => throw new Exception("Other shapes for cases types not handled")
        }
        val outType: Type = (for {
          allCaseHandlerTypes <- collectAllCaseHandlerTypes(casesDefn)
          caseHandlerOutTypes = allCaseHandlerTypes.values.map {
            case FunType(_, outType) => outType
            case _ => throw new Exception("Should not happen after type-checking")
          }.toList
          outT <- unifyTypes(caseHandlerOutTypes/*.map(subSelfInTypeAccordingTo(curPath))*/)
        } yield outT).getOrElse(throw new Exception("Should not happen after type-checking"))
        val casesDefnType: Type = FunType(envType, outType)

        val cType: Type = FunType(casesDefn.matchType, FunType(envType, outType))
        s"${pathIdentifier(curPath)(path)}.$name.asInstanceOf[${generateCodeType(curPath)(cType)}]"
    }
    case FamCases(None, _) => throw new Exception("Should not have None paths after name resolution")

    case App(e1, e2) =>
      val lhsCode = e1 match {
        case Lam(_, _, _) => s"(${generateCodeExpression(curPath)(e1)})"
        case _ => s"${generateCodeExpression(curPath)(e1)}"
      }
      val rhsCode = e2 match {
        //case Rec(fields) if fields.isEmpty => ""
        case _ => s"${generateCodeExpression(curPath)(e2)}"
      }
      s"$lhsCode($rhsCode)"

    case Rec(fields) =>
      if fields.isEmpty then "()"
        // TODO: do we need to get the types here?
      else {
        val fieldsCode =
          fields
            .map { (fieldName, fieldExp) => s"val $fieldName = ${generateCodeExpression(curPath)(fieldExp)}" }
            .mkString("; ")
        s"new Selectable {$fieldsCode}"
      }

    case Proj(e, name) =>
      val projCast: String = e.exprType match {
        case Some(famType@FamType(Some(path), name)) if getCompleteLinkageUnsafe(path).types.contains(name) =>
          s".asInstanceOf[${generateCodeType(curPath)(concretizeType(famType))}]"
        case _ => ""
      }
      s"${generateCodeExpression(curPath)(e)}$projCast.$name"

    // same as `rec`, but with defaults
    case Inst(famType@FamType(Some(path), name), Rec(fields)) =>
      val lkg = getCompleteLinkageUnsafe(path)
      val defaultFields: Map[String, Expression] = lkg.defaults.get(name) match {
        case None => Map.empty
        case Some(defaultDefn) => collectAllDefaults(defaultDefn).getOrElse(throw new Exception("Should not happen"))
      }
      val instCast: String = path match {
        case Sp(_) => s".asInstanceOf[${generateCodeType(curPath)(famType)}]"
        case _ => ""
      }
      s"${generateCodeExpression(curPath)(Rec(defaultFields ++ fields))}$instCast"
    case Inst(FamType(None, _), _) => throw new Exception("Should not have None paths after name resolution")

    case InstADT(FamType(Some(path), name), ctorName, Rec(fields)) =>
      val translationFnPathCode: String = pathIdentifier(curPath)(path) + (path match {
        case Sp(_) => ""
        case _ => ".Family"
      })
      val lkg: Linkage = getCompleteLinkageUnsafe(path)
      val adtDefn: AdtDefn =
        lkg.adts.getOrElse(name, throw new Exception("Should be defined after type-checking"))
      // TODO: can be done more efficiently if searched directly
      val ctorPath: Path = concretizePath(findPathToConstructor(adtDefn, path, ctorName).last)
      val ctorPathCode: String = pathIdentifier(curPath)(ctorPath)
      val ctorArgs: String =
        fields
          .map { (argName, argExp) => s"$argName = ${generateCodeExpression(curPath)(argExp)}" }
          .mkString(", ")

      // applies translation fn from path of T where constructor is declared to `translationFnPathCode`'s T
      s"$translationFnPathCode.$ctorPathCode$$$$$name($ctorPathCode.$ctorName($ctorArgs))"
    case InstADT(FamType(None, _), _, _) => throw new Exception("Should not have None paths after name resolution")

    // match e with <m> {} => g(())(e)
    case Match(e, g) => g match {
      case App(cases, envArg@Rec(_)) =>
        val casesCode = generateCodeExpression(curPath)(cases)
        val matchArgCode = generateCodeExpression(curPath)(e)
        val envArgCode = generateCodeExpression(curPath)(envArg)
        s"$casesCode($matchArgCode)($envArgCode)"
      case _ => throw new Exception(s"Expression $g not handled for match expressions")
    }

    case NConst(n) => n.toString
    case ABinExp(a1, op, a2) =>
      val lhsCode = generateCodeExpression(curPath)(a1)
      val rhsCode = generateCodeExpression(curPath)(a2)
      val opCode = showAOp(op)
      s"($lhsCode $opCode $rhsCode)"

    case BConst(b) => b.toString
    case BBinExp(e1, op, e2) =>
      val lhsCode = generateCodeExpression(curPath)(e1)
      val rhsCode = generateCodeExpression(curPath)(e2)
      val opCode = showBOp(op)
      s"($lhsCode $opCode $rhsCode)"
    case BNot(e) => s"!${generateCodeExpression(curPath)(e)}"

    case IfThenElse(condExpr, ifExpr, elseExpr) =>
      val condCode = generateCodeExpression(curPath)(condExpr)
      val ifCode = generateCodeExpression(curPath)(ifExpr)
      val elseCode = generateCodeExpression(curPath)(elseExpr)
      s"(if $condCode then $ifCode else $elseCode)"

    case StringLiteral(literal) => s"\"$literal\""
    case StringInterpolated(interpolated) =>  
      val inner: String = interpolated.map {
        case StringComponent(str) => str
        case InterpolatedComponent(exp) => s"$${${generateCodeExpression(curPath)(exp)}}"
      }.mkString
      s"s\"$inner\""
  }
}
