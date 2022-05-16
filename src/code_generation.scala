import famfun.*
import type_checking.{collectAllCaseHandlerTypes, collectAllDefns, getCompleteLinkage, unifyTypes}

import reflect.Selectable.reflectiveSelectable

object code_generation {
  val indent: String = "  "

  def indentBy(n: Int)(str: String): String = indent + str.flatMap {
    case '\n' => s"\n$indent"
    case c => c.toString
  }

  def linkageFileName(lkg: Linkage): String = s"${pathIdentifier(lkg.path)}.scala"

  def pathIdentifier(p: Path): String = {
    val famList = pathToFamList(p)
    p match {
      case Sp(_) => s"self$$${famList.size}"
      case AbsoluteFamily(_, _) => famList.mkString("$")
    }
  }

  def selfPathsInScope(p: Path): List[String] =
    pathToFamList(p).inits
      .toList.reverse.tail
      .map { spFams => spFams.mkString("$") }

  def generateSelfParams(p: Path): List[String] =
    selfPathsInScope(p)
      .zipWithIndex
      .map { (selfParam, i) => s"self$$${i+1}: $selfParam.Interface"}

  def findPathAdt(curDefn: AdtDefn, curPath: Path)(check: (Map[String, RecType], Path) => Boolean): List[Path] = {
    def findNext(nextPath: Path): List[Path] = {
      val nextLkg = getCompleteLinkage(nextPath)
      val nextDefn =
        nextLkg.adts.getOrElse(curDefn.name, throw new Exception("Should be defined after type-checking"))
      findPathAdt(nextDefn, nextPath)(check)
    }

    def resultIfNonNil(restResult: List[Path]): List[Path] = restResult match {
      case Nil => Nil
      case _ => curPath :: restResult
    }

    curDefn.adtBody match {
      case DefnBody(Some(curCtors), _, _) if check(curCtors, curPath) => List(curPath)
      case DefnBody(_, None, None) => Nil
      case DefnBody(_, None, Some(furtherBindsFrom)) => resultIfNonNil(findNext(furtherBindsFrom))
      case DefnBody(_, Some(extendsFrom), None) => resultIfNonNil(findNext(extendsFrom))
      case DefnBody(_, Some(extendsFrom), Some(furtherBindsFrom)) => resultIfNonNil(findNext(furtherBindsFrom)) match {
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

  // Produces a list of pairs of desired file names with the code they contain
  // generated from the complete linkages given
  def generateCode(completeLinkages: Iterable[Linkage]): Iterable[(String, String)] =
    completeLinkages
      .filter { _.self != Prog }
      .map { lkg => linkageFileName(lkg) -> generateCodeLinkage(lkg) }

  def generateCodeLinkage(lkg: Linkage): String = {
    // TODO: types with defaults?

    val curPathId = pathIdentifier(lkg.path)

    val typesCode: String = lkg.types.values.map { case typeDefn@TypeDefn(typeName, _, _) =>
      generateCodeTypeDefn(
        typeDefn,
        lkg.defaults
          .getOrElse(typeName, throw new Exception("Should exist by construction"))
          .defaultBody.defn.map(_.fields).getOrElse(Map.empty)
      )
    }.mkString("\n")

    val adtsCode: String = lkg.adts.values.map(generateCodeAdtDefn).mkString("\n")

    val interfaceCode: String = generateCodeInterface(lkg.path)(lkg.adts.values, lkg.funs.values, lkg.depot.values)
    val familyCode: String = generateCodeFamily(lkg.path)(lkg.adts.values, lkg.funs.values, lkg.depot.values)

    s"""import reflect.Selectable.reflectiveSelectable
       |
       |object $curPathId {
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

  def generateCodeInterface(curPath: Path)
                           (adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    // TODO: move this out somewhere
    def firstSome[T](opt1: Option[T], opt2: Option[T]): Option[T] = opt1 match {
      case None => opt2
      case Some(_) => opt1
    }

    val curPathId: String = pathIdentifier(curPath)

    val allBodies: Iterable[DefnBody[Expression]] = funs.map { _.funBody } ++ cases.map { _.casesBody }
    // TODO: need a more robust way of doing this; does not detect extends or further-binds relation
    //       if there is nothing to be inherited
    val optInheritPaths: (Option[Path], Option[Path]) =
      allBodies.foldLeft((Option.empty[Path], Option.empty[Path])) {
        case ((accExtends, accFurtherBinds), DefnBody(_, extendsFrom, furtherBindsFrom)) =>
          (firstSome(accExtends, extendsFrom), firstSome(accFurtherBinds, furtherBindsFrom))
      }

    val interfaceExtension: String = optInheritPaths match {
      case (None, None) => ""
      case (Some(extendsPath), None) => s"extends ${pathIdentifier(extendsPath)}.Interface"
      case (None, Some(furtherBindsPath)) => s"extends ${pathIdentifier(furtherBindsPath)}.Interface"
      case (Some(extendsPath), Some(furtherBindsPath)) =>
        s"extends ${pathIdentifier(extendsPath)}.Interface with ${pathIdentifier(furtherBindsPath)}.Interface"
    }

    val selfFields: String = generateSelfParams(curPath).map { selfWithType =>
      s"val $selfWithType"
    }.mkString("\n")

    val selfAdtsSig: String = adts.map {
      adtDefn => s"type ${adtDefn.name}"
    }.mkString("\n")

    val funsSig: String = funs.map(generateCodeFunSignature(None)).mkString("\n")

    val casesSig: String = cases.map(generateCodeCasesSignature(None)).mkString("\n")

    val translationsSig: String = adts.map { adtDefn =>
      val adtName: String = adtDefn.name
      s"def $curPathId$$$$$adtName(from: $curPathId.$adtName): $adtName"
    }.mkString("\n")

    s"""trait Interface $interfaceExtension {
       |  // Self fields
       |${indentBy(1)(selfFields)}
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

  def generateCodeFamily(curPath: Path)
                        (adts: Iterable[AdtDefn], funs: Iterable[FunDefn], cases: Iterable[CasesDefn]): String = {
    val curPathId: String = pathIdentifier(curPath)

    val selfFields: String =
      selfPathsInScope(curPath)
        .zipWithIndex
        .map { (p, i) => s"override val self$$${i+1}: $p.Interface = $p.Family"}
        .mkString("\n")

    val adtsCode: String = adts.map { adtDefn =>
      s"override type ${adtDefn.name} = ${pathIdentifier(curPath)}.${adtDefn.name}"
    }.mkString("\n")

    val funsCode: String = funs.map(generateCodeFunDefn(curPath)).mkString("\n")

    val casesCode: String = cases.map(generateCodeCasesDefn(curPath)).mkString("\n")

    val translationsCode: String = adts.map(generateCodeTranslationFunction(curPath)).mkString("\n")

    // TODO: translation functions for adt constructors in curPath too
    s"""object Family extends ${pathIdentifier(curPath)}.Interface {
       |  // Self field instantiation
       |${indentBy(1)(selfFields)}
       |
       |  // Self named types instantiation
       |  // TODO!!!
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

  def generateCodeTypeDefn(typeDefn: TypeDefn, defaults: Map[String, Expression]): String = "// TODO: type with default"

  def generateCodeAdtDefn(adtDefn: AdtDefn): String = {
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
                    case FamType(Some(p@Sp(_)), name) if getCompleteLinkage(p).adts.contains(name) =>
                      val famTypeCode = s"${pathIdentifier(p)}$$$$$name"
                      typeParams += famTypeCode
                      famTypeCode
                    case _ => generateCodeType(fieldType)
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
          val inheritPathCode = pathIdentifier(inheritPath)
          s"case class $inheritPathCode$$$$$adtName(inherited: $inheritPathCode.$adtName) extends $adtName"
        }

    s"""sealed trait $adtName
       |// Defined constructors
       |${definedCtors.mkString("\n")}
       |// Inherited constructors
       |${inheritCtors.mkString("\n")}
       |""".stripMargin
  }

  def generateCodeFunDefn(curPath: Path)(funDefn: FunDefn): String = {
    val selfArgs: String = (1 to pathToFamList(curPath).size).map { n => s"self$$$n" }.mkString(", ")

    val implBody: String = funDefn.funBody match {
      case DefnBody(None, _, Some(furtherBindsPath)) =>
        s"${pathIdentifier(furtherBindsPath)}.Family.${funDefn.name}$$Impl($selfArgs)"
      case DefnBody(None, Some(extendsPath), None) =>
        s"${pathIdentifier(extendsPath)}.Family.${funDefn.name}$$Impl($selfArgs)"
      case DefnBody(Some(expr), _, _) =>
        generateCodeExpression(curPath)(expr)
    }

    s"""override ${generateCodeFunSignature(None)(funDefn)} = ${funDefn.name}$$Impl($selfArgs)
       |${generateCodeFunSignature(Some(curPath))(funDefn)} =
       |${indentBy(1)(implBody)}""".stripMargin
  }

  // When optSelf is Some(_), generates the signature for the $Impl function
  def generateCodeFunSignature(optPath: Option[Path])(funDefn: FunDefn): String = optPath match {
    case None => s"val ${funDefn.name}: ${generateCodeType(funDefn.t)}"
    case Some(curPath) =>
      val selfParamsCode: String = generateSelfParams(curPath).mkString(", ")
      s"def ${funDefn.name}$$Impl($selfParamsCode): ${generateCodeType(funDefn.t)}"
  }

  def generateCodeCasesDefn(curPath: Path)(casesDefn: CasesDefn): String = {
    val selfArgs: String = (1 to pathToFamList(curPath).size).map { n => s"self$$$n" }.mkString(", ")

    val matchType: FamType = casesDefn.matchType
    val concreteMatchTypeCode: String = generateCodeType(concretizeType(matchType))
    val matchTypePath: Path = concretizePath(
      matchType.path
        .getOrElse(throw new Exception("Should not have None paths after name resolution"))
    )
    val matchTypePathId: String = pathIdentifier(matchTypePath)
    val matchTypePathLkg: Linkage = getCompleteLinkage(matchTypePath)
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
            // TODO: find inherit path to constructor along with constructor fields instead
            val typeArgs: Set[String] = matchTypeAdtDefn.adtBody.defn match {
              case None => throw new Exception("TODO: implement finding inherit path to constructor")
              case Some(ctors) =>
                ctors
                  .getOrElse(ctorName, throw new Exception("TODO: implement finding inherit path to constructor"))
                  .fields.values.toSet.flatMap {
                    case FamType(Some(p@Sp(_)), name) if getCompleteLinkage(p).adts.contains(name) =>
                      Set(s"${pathIdentifier(p)}.$name")
                    case _ => Set.empty
                  }
            }
            val typeArgsCode: String = if typeArgs.isEmpty then "" else s"[${typeArgs.mkString(", ")}]"

            val ignoredFields = List.fill(ctorFieldTypes.size)("_").mkString(", ")
            val instType = s"$matchTypePathId.$ctorName$typeArgsCode"
            s"""case $matchTypePathId.$ctorName($ignoredFields) =>
               |  val $instName: $instType = matched.asInstanceOf[$instType]
               |${indentBy(1)(generateCodeExpression(curPath)(handlerExp))}""".stripMargin
          case _ => throw new Exception("Other shapes for case handlers not handled")
        }
        (if v == "_" then "unused$" else v, t, clauses)
      case _ => throw new Exception("Other shapes for cases definitions not handled")
    }

    val inheritedClauses: List[String] =
      List(casesDefn.casesBody.extendsFrom, casesDefn.casesBody.furtherBindsFrom)
        .collect { case Some(inheritPath) =>
          val inheritPathCode = pathIdentifier(inheritPath)
          s"""case $matchTypePathId.$inheritPathCode$$$$${matchType.name}(inherited) =>
             |  $inheritPathCode.Family.${casesDefn.name}$$Impl($selfArgs)(inherited)($envParamName)""".stripMargin
        }

    // TODO: all clauses
    val caseClauses: List[String] = definedClauses ++ inheritedClauses

    s"""${generateCodeCasesSignature(None)(casesDefn)} = ${casesDefn.name}$$Impl($selfArgs)(matched.asInstanceOf[$concreteMatchTypeCode])
       |${generateCodeCasesSignature(Some(curPath))(casesDefn)} = ($envParamName: ${generateCodeType(envParamType)}) => matched match {
       |${indentBy(1)(caseClauses.mkString("\n"))}
       |}""".stripMargin
  }

  // When optSelf is Some(_), generates the signature for the $Impl function
  def generateCodeCasesSignature(optPath: Option[Path])(casesDefn: CasesDefn): String = {
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
      outT <- unifyTypes(caseHandlerOutTypes)
    } yield outT).getOrElse(throw new Exception("Should not happen after type-checking"))
    val casesDefnType: Type = FunType(envType, outType)

    optPath match {
      case None =>
        s"def ${casesDefn.name}(matched: ${generateCodeType(casesDefn.matchType)}): ${generateCodeType(casesDefnType)}"
      case Some(curPath) =>
        val concreteMatchType = concretizeType(casesDefn.matchType)
        val selfParamsCode: String = generateSelfParams(curPath).mkString(", ")
        s"def ${casesDefn.name}$$Impl($selfParamsCode)(matched: ${generateCodeType(concreteMatchType)}): ${generateCodeType(casesDefnType)}"
    }
  }

  def generateCodeTranslationFunction(curPath: Path)(adtDefn: AdtDefn): String = {
    def ctorCallPath(pathList: List[Path]): List[String] = pathList match {
      case p1 :: p2 :: ps => s"${pathIdentifier(p1)}.${pathIdentifier(p2)}$$$$${adtDefn.name}" :: ctorCallPath(p2 :: ps)
      case _ => Nil
    }

    val curPathId: String = pathIdentifier(curPath)

    // Collect all paths from which this adt extends a definition
    val (inheritedPaths, _) = collectAllDefns(adtDefn)(_.adtBody) { lkg =>
      lkg.adts
        .getOrElse(adtDefn.name, throw new Exception(s"${lkg.self} should contain an ADT definition for ${adtDefn.name} by construction"))
    } { _ => () } (()) { (_, _) => () }

    val allPaths = curPath :: inheritedPaths.toList

    allPaths.map { targetPath =>
      val targetPathId: String = pathIdentifier(targetPath)
      // TODO: find target paths and generate translation terms at once to be more efficient
      val ctorCalls = ctorCallPath(findPathToPath(adtDefn, curPath, targetPath))
      val translationTerm: String = ctorCalls.foldRight("from") { (c, r) =>
        s"$c($r)"
      }
      s"def $targetPathId$$$$${adtDefn.name}(from: $targetPathId.${adtDefn.name}): ${adtDefn.name} = $translationTerm"
    }.mkString("\n")
  }

  def generateCodeType(t: Type): String = t match {
    case N => "Int"
    case B => "Boolean"
    case FamType(Some(p), name) => s"${pathIdentifier(p)}.$name"
    case FamType(None, name) => throw new Exception("Should not have None paths after name resolution")
    case FunType(input, output) => s"${generateCodeType(input)} => ${generateCodeType(output)}"
    case RecType(fields) =>
      if fields.isEmpty then "Unit"
      else {
        val fieldsCode =
          fields
            .map { (fieldName, fieldType) => s"val $fieldName: ${generateCodeType(fieldType)}" }
            .mkString("; ")

        s"{$fieldsCode}"
      }
  }

  def generateCodeExpression(curPath: Path)(e: Expression): String = e match {
    case Var(id) => id

    case Lam(Var(v), t, body) => s"($v: ${generateCodeType(t)}) => ${generateCodeExpression(curPath)(body)}"

    case FamFun(Some(path), name) => path match {
      case AbsoluteFamily(_, _) =>
        val selfArgs: String = selfPathsInScope(path).map(_ ++ ".Family").mkString(", ")
        s"${pathIdentifier(path)}.Family.$name$$Impl($selfArgs)"
      case Sp(_) =>
        // TODO: only cast if needed (fType contains relative types)
        val lkg: Linkage = getCompleteLinkage(path)
        val fType: Type = lkg.funs.getOrElse(name, throw new Exception("Should exist after type checking")).t
        s"${pathIdentifier(path)}.$name.asInstanceOf[${generateCodeType(fType)}]"
    }
    case FamFun(None, _) => throw new Exception("Should not have None paths after name resolution")

    case FamCases(Some(path), name) => path match {
      case AbsoluteFamily(_, _) =>
        val selfArgs: String = selfPathsInScope(path).map(_ ++ ".Family").mkString(", ")
        s"${pathIdentifier(path)}.Family.$name$$Impl($selfArgs)"
      case Sp(_) =>
        // TODO: only cast if needed (fType contains relative types)
        val lkg: Linkage = getCompleteLinkage(path)
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
          outT <- unifyTypes(caseHandlerOutTypes)
        } yield outT).getOrElse(throw new Exception("Should not happen after type-checking"))
        val casesDefnType: Type = FunType(envType, outType)

        val cType: Type = FunType(casesDefn.matchType, FunType(envType, outType))
        s"${pathIdentifier(path)}.$name.asInstanceOf[${generateCodeType(cType)}]"
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

    case Proj(e, name) => s"${generateCodeExpression(curPath)(e)}.$name"

    case Inst(t, rec) =>
      // same as `rec`, but with defaults
      "TODO: named type instance"

    case InstADT(FamType(Some(path), name), ctorName, Rec(fields)) =>
      val translationFnPathCode: String = pathIdentifier(path) + (path match {
        case Sp(_) => ""
        case _ => ".Family"
      })
      // TODO: find family p.A where constructor ctorName came from instread
      val lkg: Linkage = getCompleteLinkage(path)
      val adtDefn: AdtDefn =
        lkg.adts.getOrElse(name, throw new Exception("Should be defined after type-checking"))
      // TODO: can be done more efficiently if searched directly
      val ctorPath: Path = concretizePath(findPathToConstructor(adtDefn, path, ctorName).last)
      val ctorPathCode: String = pathIdentifier(ctorPath)
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

    case Nexp(n) => n.toString

    case Bexp(b) => b.toString
  }
}
