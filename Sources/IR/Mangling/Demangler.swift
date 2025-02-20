import FrontEnd

/// Hylo's demangling algorithm.
struct Demangler {

  /// The list of demangled strings, in order of appearance (a.k.a. the string lookup table).
  private var strings: [Substring] = []

  /// The list of demangled symbols, in order of appearance (a.k.a. the symbol lookup table).
  private var symbols: [DemangledSymbol] = []

  /// Creates an instance with an empty lookup table.
  init() {}

  /// Demangles a symbol from `stream`.
  mutating func demangle(from stream: inout Substring) -> DemangledSymbol? {
    var qualification: DemangledQualification? = nil

    while let o = takeOperator(from: &stream) {
      let demangled: DemangledSymbol?

      switch o {
      case .anonymousScope:
        demangled = takeAnonymousScope(qualifiedBy: qualification, from: &stream)
      case .arrowType:
        demangled = takeArrowType(from: &stream)
      case .associatedType:
        demangled = takeAssociatedType(from: &stream)
      case .associatedTypeDecl:
        demangled = take(AssociatedTypeDecl.self, qualifiedBy: qualification, from: &stream)
      case .associatedValueDecl:
        demangled = take(AssociatedValueDecl.self, qualifiedBy: qualification, from: &stream)
      case .bindingDecl:
        demangled = takeBindingDecl(qualifiedBy: qualification, from: &stream)
      case .boundGenericType:
        demangled = takeBoundGenericType(from: &stream)
      case .bufferType:
        demangled = takeBufferType(from: &stream)
      case .builtinIntegerType:
        demangled = takeBuiltinIntegerType(from: &stream)
      case .builtinFloatType:
        demangled = takeBuiltinFloatType(from: &stream)
      case .builtinPointerType:
        demangled = .type(.builtin(.ptr))
      case .builtinModuleType:
        demangled = .type(.builtin(.module))
      case .builtinWordType:
        demangled = .type(.builtin(.word))
      case .conformanceDecl:
        demangled = take(ConformanceDecl.self, qualifiedBy: qualification, from: &stream)
      case .directDeclReference:
        demangled = takeDirectDeclReference(from: &stream)
      case .endOfSequence:
        demangled = nil
      case .existentialMetatype:
        demangled = .type(.anyMetatype)
      case .existentialGenericType:
        demangled = takeExistentialGenericType(from: &stream)
      case .existentialTraitType:
        demangled = takeExistentialTraitType(from: &stream)
      case .extensionDecl:
        demangled = take(ExtensionDecl.self, qualifiedBy: qualification, from: &stream)
      case .functionDecl:
        demangled = takeFunctionDecl(qualifiedBy: qualification, from: &stream)
      case .genericParameterDecl:
        demangled = take(GenericParameterDecl.self, qualifiedBy: qualification, from: &stream)
      case .genericTypeParameterType:
        demangled = takeNominalType(declaredBy: GenericParameterDecl.self, from: &stream)
      case .importDecl:
        demangled = take(ImportDecl.self, qualifiedBy: qualification, from: &stream)
      case .lookup:
        demangled = takeLookup(from: &stream)
      case .memberwiseInitializerDecl:
        demangled = takeMemberwiseInitializerDecl(qualifiedBy: qualification, from: &stream)
      case .metatypeType:
        demangled = takeMetatypeType(from: &stream)
      case .moduleDecl:
        demangled = takeModuleDecl(from: &stream)
      case .monomorphizedFunctionDecl:
        demangled = takeMonomorphizedFunctionDecl(from: &stream)
      case .namespaceDecl:
        demangled = take(NamespaceDecl.self, qualifiedBy: qualification, from: &stream)
      case .parameterDecl:
        demangled = take(ParameterDecl.self, qualifiedBy: qualification, from: &stream)
      case .parameterType:
        demangled = takeParameterType(from: &stream)
      case .productType:
        demangled = takeNominalType(declaredBy: ProductTypeDecl.self, from: &stream)
      case .propertyDecl:
        demangled = takePropertyDecl(qualifiedBy: qualification, from: &stream)
      case .productTypeDecl:
        demangled = take(ProductTypeDecl.self, qualifiedBy: qualification, from: &stream)
      case .remoteType:
        demangled = takeRemoteType(from: &stream)
      case .reserved:
        demangled = takeReserved(from: &stream)
      case .staticFunctionDecl:
        demangled = takeFunctionDecl(qualifiedBy: qualification, from: &stream)
      case .subscriptDecl:
        demangled = takeSubscriptDecl(qualifiedBy: qualification, from: &stream)
      case .subscriptImpl:
        demangled = takeSubscriptImpl(qualifiedBy: qualification, from: &stream)
      case .subscriptType:
        demangled = takeSubscriptType(from: &stream)
      case .synthesizedFunctionDecl:
        demangled = takeSynthesizedFunctionDecl(from: &stream)
      case .traitDecl:
        demangled = take(TraitDecl.self, qualifiedBy: qualification, from: &stream)
      case .traitType:
        demangled = takeNominalType(declaredBy: TraitDecl.self, from: &stream)
      case .translatonUnit:
        demangled = take(TranslationUnit.self, qualifiedBy: qualification, from: &stream)
      case .tupleType:
        demangled = takeTupleType(from: &stream)
      case .typealiasDecl:
        demangled = take(TypeAliasDecl.self, qualifiedBy: qualification, from: &stream)
      case .unionType:
        demangled = takeUnionType(from: &stream)
      case .varDecl:
        demangled = take(VarDecl.self, qualifiedBy: qualification, from: &stream)

      case .lookupRelative:
        qualification = .relative
        continue

      case .subscriptImplType:
        fatalError()

      case .existentializedFunctionDecl:
        return nil
      case .methodDecl:
        return nil
      case .methodImpl:
        return nil
      case .methodType:
        return nil
      case .conformanceConstraint, .equalityConstraint, .valueConstraint, .whereClause:
        return nil
      case .witnessTable:
        return nil
      }

      // End of sequence reached if `demangled` is `nil`.
      guard let d = demangled else { break }
      if (o != .lookup) && (o != .lookupRelative) && (o != .reserved) {
        symbols.append(d)
      }

      // Update the context and look for the next symbol if we demangled a scope.
      if let e = d.entity, e.isScope {
        qualification = .entity(e)
        continue
      }

      // Otherwise, we're done.
      return d
    }

    if let e = qualification?.entity {
      return .entity(e)
    } else {
      return nil
    }
  }

  /// Demangles an entity of type `T` from `stream`.
  private mutating func demangleEntity<T: Node>(
    _: T.Type, from stream: inout Substring
  ) -> DemangledEntity? {
    if case .entity(let e) = demangle(from: &stream), e.kind?.value == T.self {
      return e
    } else {
      return nil
    }
  }

  /// Demangles a type from `stream`.
  private mutating func demangleType(from stream: inout Substring) -> DemangledType? {
    if case .type(let t) = demangle(from: &stream) {
      return t
    } else {
      return nil
    }
  }

  /// Demangles an entity declaration of type `T` from `stream`.
  private mutating func take<T: Node>(
    _: T.Type, qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let s = takeString(from: &stream)
    else { return nil }
    return .entity(.init(qualification: q, kind: NodeKind(T.self), name: Name(stem: String(s))))
  }

  /// Demangles an conformance declaration from `stream`.
  private mutating func take<T: TypeExtendingDecl>(
    _: T.Type, qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let s = demangleType(from: &stream),
      let o = takeOperator(from: &stream)
    else { return nil }

    switch o {
    case .endOfSequence:
      break
    case .whereClause:
      UNIMPLEMENTED()
    default:
      return nil
    }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(T.self),
      name: Name(stem: s.description))
    return .entity(e)
  }

  /// Demangles an anonymous scope from `stream`.
  private mutating func takeAnonymousScope(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let i = takeInteger(from: &stream)
    else { return nil }
    return .entity(.init(anonymousScope: Int(i.rawValue), qualifiedBy: q))
  }

  /// Demangles a binding declaration from `stream`.
  private mutating func takeBindingDecl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    let vs = takeItems(from: &stream) { (me, s) in
      me.demangle(from: &s)?.entity
    }
    return vs.map({ (ns) in .binding(names: ns) })
  }

  /// Demangles a function from `stream`.
  private mutating func takeFunctionDecl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let name = takeName(from: &stream),
      let genericParameterCount = takeInteger(from: &stream),
      let type = demangleType(from: &stream)
    else { return nil }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(FunctionDecl.self),
      name: name,
      genericArgumentLabels: .init(repeating: nil, count: Int(genericParameterCount.rawValue)),
      type: type)
    return .entity(e)
  }

  /// Demangles a synthesized function from `stream`.
  private mutating func takeSynthesizedFunctionDecl(
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let k = takeSynthesizedFunctionDeclKind(from: &stream),
      let s = demangle(from: &stream),
      let t = demangleType(from: &stream)
    else { return nil }
    return .synthesized(.init(type: t, scope: .init(s), kind: k))
  }

  /// Demangles the kind of a synthesized function from `stream`.
  private mutating func takeSynthesizedFunctionDeclKind(
    from stream: inout Substring
  ) -> DemangledSynthesizedFunction.Kind? {
    guard let k = takeBase64Digit(from: &stream) else { return nil }
    switch k.rawValue {
    case 0: return .deinitialize
    case 1: return .moveInitialization
    case 2: return .moveAssignment
    case 3: return .copy
    case 4: return .equal
    case 5: return takeSynthesizedGlobalInitializationKind(from: &stream)
    case 6: return takeSynthesizedAutoclosureKind(from: &stream)
    default: return nil
    }
  }

  /// Demangles the kind of a synthesized global initializer from `stream`.
  private mutating func takeSynthesizedGlobalInitializationKind(
    from stream: inout Substring
  ) -> DemangledSynthesizedFunction.Kind? {
    demangle(from: &stream).map { (d) in
      DemangledSynthesizedFunction.Kind.globalInitialization(d)
    }
  }

  /// Demangles the kind of a synthesized autoclosure from `stream`.
  private func takeSynthesizedAutoclosureKind(
    from stream: inout Substring
  ) -> DemangledSynthesizedFunction.Kind? {
    takeInteger(from: &stream).map { (n) in
      DemangledSynthesizedFunction.Kind.autoclosure(Int(n.rawValue))
    }
  }

  /// Demangles a monomorphized function from `stream`.
  private mutating func takeMonomorphizedFunctionDecl(
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let f = demangle(from: &stream),
      let z = takeGenericArguments(from: &stream)
    else { return nil }
    return .monomorphized(f, arguments: z)
  }

  /// Demangles a memberwise initializer from `stream`.
  private func takeMemberwiseInitializerDecl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification
    else { return nil }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(InitializerDecl.self),
      name: Name(stem: "init"))
    return .entity(e)
  }

  /// Demangles a module from `stream`.
  private mutating func takeModuleDecl(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let s = takeString(from: &stream)
    else { return nil }

    let e = DemangledEntity(
      qualification: nil, kind: NodeKind(ModuleDecl.self), name: Name(stem: String(s)))
    return .entity(e)
  }

  /// Demangles a property declaration from `stream`.
  private mutating func takePropertyDecl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let stem = takeString(from: &stream),
      let type = demangleType(from: &stream)
    else { return nil }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(SubscriptDecl.self),
      name: Name(stem: String(stem)),
      type: type)
    return .entity(e)
  }

  /// Demangles a property declaration from `stream`.
  private mutating func takeSubscriptDecl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let stem = takeString(from: &stream),
      let genericParameterCount = takeInteger(from: &stream),
      let type = demangleType(from: &stream)
    else { return nil }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(SubscriptDecl.self),
      name: Name(stem: stem.isEmpty ? "[]" : String(stem)),
      genericArgumentLabels: .init(repeating: nil, count: Int(genericParameterCount.rawValue)),
      type: type)
    return .entity(e)
  }

  /// Demangles a property declaration from `stream`.
  private mutating func takeSubscriptImpl(
    qualifiedBy qualification: DemangledQualification?,
    from stream: inout Substring
  ) -> DemangledSymbol? {
    guard
      let q = qualification,
      let a = take(AccessEffect.self, from: &stream)
    else { return nil }

    let e = DemangledEntity(
      qualification: q,
      kind: NodeKind(SubscriptImpl.self),
      name: Name(stem: "\(a)"))
    return .entity(e)
  }

  /// Demangles a direct declaration reference from `stream`.
  private mutating func takeDirectDeclReference(from stream: inout Substring) -> DemangledSymbol? {
    UNIMPLEMENTED()
  }

  /// Demangles a reference to a symbol from `stream`.
  private mutating func takeLookup(from stream: inout Substring) -> DemangledSymbol? {
    takeInteger(from: &stream).flatMap({ (n) in symbols[Int(n.rawValue)] })
  }

  /// Demangles a reserved symbol from `stream`.
  private mutating func takeReserved(from stream: inout Substring) -> DemangledSymbol? {
    take(ReservedSymbol.self, from: &stream).map(DemangledSymbol.init(reserved:))
  }

  /// Demangles an associated type from `stream`.
  private mutating func takeAssociatedType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let d = demangleType(from: &stream),
      let n = demangleEntity(AssociatedTypeDecl.self, from: &stream)
    else { return nil }
    return .type(.associatedType(domain: d, name: n.name.stem))
  }

  /// Demangles a bound generic type from `stream`.
  private mutating func takeBoundGenericType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let b = demangleType(from: &stream),
      let z = takeGenericArguments(from: &stream)
    else { return nil }

    return .type(.boundGeneric(base: b, arguments: z))
  }

  /// Demangles a list of generic arguments from `stream`.
  private mutating func takeGenericArguments(from stream: inout Substring) -> [DemangledSymbol]? {
    takeItems(from: &stream, takingEachWith: { (me, s) in me.demangle(from: &s) })
  }

  /// Demangles a buffer type from `stream`.
  private mutating func takeBufferType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let element = demangleType(from: &stream),
      let count = takeInteger(from: &stream)  // TODO: arbitrary compile-time values
    else { return nil }
    return .type(.buffer(element: element, count: Int(count.rawValue)))
  }

  /// Demangles a built-in integer type from `stream`.
  private mutating func takeBuiltinIntegerType(from stream: inout Substring) -> DemangledSymbol? {
    takeInteger(from: &stream).map({ (w) in .type(.builtin(.i(Int(w.rawValue)))) })
  }

  /// Demangles a built-in float type from `stream`.
  private mutating func takeBuiltinFloatType(from stream: inout Substring) -> DemangledSymbol? {
    switch takeInteger(from: &stream)?.rawValue {
    case .some(16):
      return .type(.builtin(.float16))
    case .some(32):
      return .type(.builtin(.float32))
    case .some(64):
      return .type(.builtin(.float64))
    case .some(128):
      return .type(.builtin(.float128))
    default:
      return nil
    }
  }

  /// Demangles an existential generic type from `stream`.
  private mutating func takeExistentialGenericType(
    from stream: inout Substring
  ) -> DemangledSymbol? {
    demangleType(from: &stream).map({ (i) in .type(.existentialGeneric(i)) })
  }

  /// Demangles an existential generic type from `stream`.
  private mutating func takeExistentialTraitType(
    from stream: inout Substring
  ) -> DemangledSymbol? {
    let ts = takeItems(from: &stream) { (me, s) in
      me.demangleType(from: &s)
    }
    return ts.map({ (s) in .type(.existentialTrait(s)) })
  }

  /// Demangles an arrow type from `stream`.
  private mutating func takeArrowType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let environment = demangleType(from: &stream),
      let inputs = takeParameters(from: &stream),
      let output = demangleType(from: &stream)
    else { return nil }

    return .type(.arrow(effect: .let, environment: environment, inputs: inputs, output: output))
  }

  /// Demangles a nominal type declared as an entity of type `T` from `stream`.
  private mutating func takeNominalType<T: SingleEntityDecl>(
    declaredBy _: T.Type, from stream: inout Substring
  ) -> DemangledSymbol? {
    demangleEntity(T.self, from: &stream).map({ (e) in .type(.nominal(e)) })
  }

  /// Demangles a metatype from `stream`.
  private mutating func takeMetatypeType(from stream: inout Substring) -> DemangledSymbol? {
    demangleType(from: &stream).map({ (t) in .type(.metatype(t)) })
  }

  /// Demangles a parameter type from `stream`.
  private mutating func takeParameterType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let a = take(AccessEffect.self, from: &stream),
      let b = demangleType(from: &stream)
    else { return nil }
    return .type(.parameter(access: a, value: b))
  }

  /// Demangles a remote type from `stream`.
  private mutating func takeRemoteType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let a = take(AccessEffect.self, from: &stream),
      let b = demangleType(from: &stream)
    else { return nil }
    return .type(.remote(access: a, value: b))
  }

  /// Demangles a subscript type from `stream`.
  private mutating func takeSubscriptType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let capabilities = take(AccessEffectSet.self, from: &stream),
      let environment = demangleType(from: &stream),
      let inputs = takeParameters(from: &stream),
      let output = demangleType(from: &stream)
    else { return nil }

    let t = DemangledType.subscriptBundle(
      capabilities: capabilities, environment: environment, inputs: inputs, output: output)
    return .type(t)
  }

  /// Demangles a tuple type from `stream`.
  private mutating func takeTupleType(from stream: inout Substring) -> DemangledSymbol? {
    takeParameters(from: &stream).map({ (s) in .type(.tuple(s)) })
  }

  /// Demangles a union type from `stream`.
  private mutating func takeUnionType(from stream: inout Substring) -> DemangledSymbol? {
    guard
      let elementCount = takeInteger(from: &stream)
    else { return nil }

    var elements: [DemangledType] = []
    elements.reserveCapacity(Int(elementCount.rawValue))
    for _ in 0..<elementCount.rawValue {
      // Elements only do not share the same symbol lookup table; only a prefix.
      var d = self
      guard
        let e = d.demangleType(from: &stream)
      else { return nil }
      elements.append(e)
    }

    return .type(.union(elements))
  }

  /// Demangles a list of parameters or tuple elements from `stream`.
  private mutating func takeParameters(
    from stream: inout Substring
  ) -> [DemangledType.Parameter]? {
    takeItems(from: &stream, takingEachWith: { (me, s) in me.takeParameter(from: &s) })
  }

  /// Demangles a parameter or tuple element from `stream`.
  private mutating func takeParameter(from stream: inout Substring) -> DemangledType.Parameter? {
    guard
      let l = takeString(from: &stream),
      let t = demangleType(from: &stream)
    else { return nil }
    return .init(label: l.isEmpty ? nil : String(l), type: t)
  }

  /// If `stream` starts with a mangling operator, consumes and returns it; returns
  /// `nil` without mutating `stream` otherwise.
  private func takeOperator(from stream: inout Substring) -> ManglingOperator? {
    if stream.isEmpty { return nil }

    var i = stream.startIndex
    if stream[i].isASCII && stream[i].isLowercase {
      i = stream.index(after: i)
      if i == stream.endIndex { return nil }
    }

    if let o = ManglingOperator(rawValue: String(stream[...i])) {
      stream = stream[stream.index(after: i)...]
      return o
    } else {
      return nil
    }
  }

  /// Assuming `stream` starts with a mangled name, consumes and returns it. Returns `nil` iff
  /// data seems corrupted
  private mutating func takeName(from stream: inout Substring) -> Name? {
    guard let tag = takeBase64Digit(from: &stream) else {
      return nil
    }

    let notation: OperatorNotation?
    if (tag.rawValue & 1) != 0 {
      guard let n = take(OperatorNotation.self, from: &stream) else { return nil }
      notation = n
    } else {
      notation = nil
    }

    let introducer: AccessEffect?
    if (tag.rawValue & 2) != 0 {
      guard let i = take(AccessEffect.self, from: &stream) else { return nil }
      introducer = i
    } else {
      introducer = nil
    }

    guard let stem = takeString(from: &stream) else {
      return nil
    }

    return Name(stem: String(stem), labels: [], notation: notation, introducer: introducer)
  }

  /// Assuming `stream` starts with a mangled string, consumes and returns it. Returns `nil` iff
  ///the data seems corrupted
  private mutating func takeString(from stream: inout Substring) -> Substring? {
    switch takeInteger(from: &stream)?.rawValue {
    case .some(0):
      return stream[stream.startIndex..<stream.startIndex]
    case .some(1):
      return takeInteger(from: &stream).flatMap({ (m) in strings[Int(m.rawValue)] })
    case .some(let n):
      let j = stream.index(stream.startIndex, offsetBy: Int(n - 2))
      let r = stream[..<j]
      strings.append(r)
      stream = stream[j...]
      return r
    default:
      return nil
    }
  }

  /// Assuming `stream` starts with a mangled integer, consumes and returns it; returns `nil`
  /// otherwise.
  private func takeInteger(from stream: inout Substring) -> Base64VarUInt? {
    guard let (v, i) = Base64VarUInt.decode(from: stream) else {
      return nil
    }
    stream = stream[i...]
    return v
  }

  /// Assuming `stream` starts with a base 64 digit, consumes and returns it. Returns `nil` iff
  /// data seems corrupted
  private func takeBase64Digit(from stream: inout Substring) -> Base64Digit? {
    stream.popFirst().flatMap(Base64Digit.init(_:))
  }

  /// Assuming `stream` starts with a mangled `T`, consumes and returns it. Returns `nil` iff
  /// data seems corrupted
  private func take<T: RawRepresentable>(
    _: T.Type, from stream: inout Substring
  ) -> T? where T.RawValue == UInt8 {
    takeBase64Digit(from: &stream).flatMap({ (d) in T(rawValue: d.rawValue) })
  }

  /// Demangles a list of `T`s from `stream`, calling `takeItem` to parse each individual element.
  private mutating func takeItems<T>(
    from stream: inout Substring,
    takingEachWith takeItem: (inout Self, inout Substring) -> T?
  ) -> [T]? {
    guard let n = takeInteger(from: &stream) else { return nil }
    var xs: [T] = []
    xs.reserveCapacity(Int(n.rawValue))

    for _ in 0..<n.rawValue {
      guard let x = takeItem(&self, &stream) else { return nil }
      xs.append(x)
    }
    return xs
  }

}
