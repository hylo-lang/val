import Utils

/// An abstract syntax tree.
public struct AST {

  /// A function inserting the contents of a module in `ast`, registering the identities of newly
  /// formed ASTs in `nodeSpace` and reporting diagnostics to `log`.
  public typealias ModuleLoader = (
    _ ast: inout AST, _ log: inout DiagnosticSet, _ nodeSpace: Int
  ) throws -> ModuleDecl.ID

  /// The stored representation of an AST; distinguished for encoding/decoding purposes.
  private struct Storage: Codable {

    /// The nodes in `self`.
    public var nodes: [[AnyNode]] = []

    /// The indices of the modules in the AST.
    ///
    /// Indices are ordered by module dependency. If `i` and `j` are the indices of two modules `A`
    /// and `B`, respectively, and `A` depends on `B`, then `i` precedes `j` in this property.
    ///
    /// - Invariant: All referred modules have a different name.
    public var modules: [ModuleDecl.ID] = []

    /// The traits in Hylo's standard library that are known by the compiler.
    var coreTraits: CoreTraits?

    /// The module containing Hylo's core library, if any.
    public var coreLibrary: ModuleDecl.ID?

    /// Conditions for selecting conditional compilation branches.
    public let compilationConditions: ConditionalCompilationFactors

    /// Creates an empty instance, using `compilationConditions` as conditions for selecting
    /// conditional compilation branches.
    public init(_ compilationConditions: ConditionalCompilationFactors) {
      self.compilationConditions = compilationConditions
    }

  }

  /// The notional stored properties of `self`; distinguished for encoding/decoding purposes.
  private var storage: Storage

  /// The traits in Hylo's standard library that are known by the compiler.
  public var coreTraits: CoreTraits? {
    get { storage.coreTraits }
    set { storage.coreTraits = newValue }
    _modify { yield &storage.coreTraits }
  }

  /// The indices of the modules.
  ///
  /// - Invariant: All referred modules have a different name.
  public private(set) var modules: [ModuleDecl.ID] {
    get { storage.modules }
    set { storage.modules = newValue }
    _modify { yield &storage.modules }
  }

  /// The module containing Hylo's core library, if any.
  public var coreLibrary: ModuleDecl.ID? {
    get { storage.coreLibrary }
    set { storage.coreLibrary = newValue }
  }

  /// The expansion filter used while processing conditional compilation statements in `self`.
  public var compilationConditions: ConditionalCompilationFactors {
    storage.compilationConditions
  }

  /// Creates an empty AST, using using `compilationConditions` as conditions for selecting
  /// conditional compilation branches.
  public init(
    _ compilationConditions: ConditionalCompilationFactors = ConditionalCompilationFactors()
  ) {
    self.storage = Storage(compilationConditions)
  }

  /// Creates a new node space and returns its identifier.
  public mutating func createNodeSpace() -> Int {
    storage.nodes.append([])
    return storage.nodes.count - 1
  }

  /// Loads a new module in `self`, calling `make` to parse its contents and reporting
  /// diagnostics to `log`.
  public mutating func loadModule(
    inNodeSpace space: Int? = nil,
    reportingDiagnosticsTo log: inout DiagnosticSet,
    creatingContentsWith parseSources: ModuleLoader
  ) rethrows -> ModuleDecl.ID {
    try parseSources(&self, &log, space ?? createNodeSpace())
  }

  /// Loads a new module in `self`, parsing its contents from `sourceCode`, registering the
  /// identities of newly formed ASTs in space `space`, and reporting diagnostics to `log`.
  ///
  /// - Parameters:
  ///   - name: The name of the loaded module.
  ///   - sourceCode: The URL of a single source file or the root directory of the module.
  ///   - space: The space in which the module's ASTs are registered. This argument should be `nil`
  ///     unless this method is called in a module loader.
  ///   - builtinModuleAccess: Whether the module is allowed to access the builtin module.
  ///   - log: A set extended with the diagnostics reported by this method.
  public mutating func loadModule<S: Sequence>(
    _ name: String, parsing sourceCode: S, inNodeSpace space: Int? = nil,
    withBuiltinModuleAccess builtinModuleAccess: Bool = false,
    reportingDiagnosticsTo log: inout DiagnosticSet,
    profileWith profiler: ProfilingMeasurements? = nil
  ) throws -> ModuleDecl.ID where S.Element == SourceFile {
    try loadModule(reportingDiagnosticsTo: &log) { (me, log, k) in
      // Suppress thrown diagnostics until all files are parsed.
      let translations = sourceCode.compactMap { (f) in
        try? Parser.parse(f, inNodeSpace: k, in: &me, diagnostics: &log, profileWith: profiler)
      }

      let m = me.insert(
        ModuleDecl(name, sources: translations, builtinModuleAccess: builtinModuleAccess),
        inNodeSpace: k,
        reportingDiagnosticsTo: &log)
      try log.throwOnError()
      return m
    }
  }

  /// Inserts `n` into `self`, registering its identity in space `k` and reporting well-formedness
  /// issues to `log`.
  public mutating func insert<T: Node>(
    _ n: T, inNodeSpace k: Int, reportingDiagnosticsTo log: inout DiagnosticSet
  ) -> T.ID {
    n.validateForm(in: self, reportingDiagnosticsTo: &log)

    let i = T.ID(rawValue: .init(base: k, offset: storage.nodes[k].count))
    if let n = n as? ModuleDecl {
      precondition(
        !modules.contains(where: { self[$0].baseName == n.baseName }), "duplicate module")
      modules.append(i as! ModuleDecl.ID)
    }
    storage.nodes[k].append(AnyNode(n))
    return i
  }

  /// Inserts `n` into `self`, registering its identity in space `k`.
  ///
  /// - Precondition: `n` is well formed.
  public mutating func insert<T: Node>(synthesized n: T, inNodeSpace k: Int) -> T.ID {
    var d = DiagnosticSet()
    let r = insert(n, inNodeSpace: k, reportingDiagnosticsTo: &d)
    precondition(d.elements.isEmpty, "ill-formed synthesized node \(n)\n\(d)")
    return r
  }

  // MARK: Node access

  /// Accesses the node identified by `i`.
  public subscript<T: ConcreteNodeID>(i: T) -> T.Subject {
    storage.nodes[i.rawValue.base][i.rawValue.offset].node as! T.Subject
  }

  /// Accesses the node identified by `i`.
  public subscript<T: ConcreteNodeID>(i: T?) -> T.Subject? {
    i.map({ (j) in storage.nodes[j.rawValue.base][j.rawValue.offset].node as! T.Subject })
  }

  /// Accesses the node identified by `i`.
  public subscript<T: NodeIDProtocol>(i: T) -> Node {
    storage.nodes[i.rawValue.base][i.rawValue.offset].node
  }

  /// Accesses the node identified by `i`.
  public subscript<T: NodeIDProtocol>(i: T?) -> Node? {
    i.map({ (j) in storage.nodes[j.rawValue.base][j.rawValue.offset].node })
  }

  /// A sequence of concrete nodes projected from an AST.
  public typealias ConcreteProjectedSequence<T> = LazyMapSequence<
    LazySequence<T>.Elements,
    T.Element.Subject
  > where T: Sequence, T.Element: ConcreteNodeID

  /// Projects a sequence containing the nodes at `positions`.
  public subscript<T: Sequence>(positions: T) -> ConcreteProjectedSequence<T> {
    positions.lazy.map({ (n) in self[n] })
  }

  // MARK: Core library

  /// Indicates whether the Core library has been loaded.
  public var coreModuleIsLoaded: Bool { coreLibrary != nil }

  /// Returns the Hylo type of an optional `t`.
  ///
  /// - Requires: The Core library must have been loaded.
  public func optional(_ t: AnyType) -> UnionType {
    let none = coreType("None")!
    let p = self[none.decl].genericParameters[0]
    let u = BoundGenericType(none, arguments: [p: .type(t)])
    return UnionType([t, ^u])
  }

  /// Returns the Hylo type of an array of `t`.
  ///
  /// - Requires: The Core library must have been loaded.
  public func array(_ t: AnyType) -> BoundGenericType {
    let b = coreType("Array")!
    let e = self[b.decl].genericParameters[0]
    return BoundGenericType(b, arguments: [e: .type(t)])
  }

  /// Returns the type named `name` defined in the core library or `nil` it does not exist.
  ///
  /// - Requires: The Core library must have been loaded.
  public func coreType(_ name: String) -> ProductType? {
    precondition(coreModuleIsLoaded, "Core library is not loaded")

    for d in topLevelDecls(coreLibrary!) where d.kind == ProductTypeDecl.self {
      let d = ProductTypeDecl.ID(d)!
      if self[d].baseName == name {
        return ProductType(d, ast: self)
      }
    }

    return nil
  }

  /// Returns the trait named `name` defined in the core library or `nil` if it does not exist.
  ///
  /// - Requires: The Core library must have been loaded.
  public func coreTrait(_ name: String) -> TraitType? {
    precondition(coreModuleIsLoaded, "Core library is not loaded")

    for id in topLevelDecls(coreLibrary!) where id.kind == TraitDecl.self {
      let id = TraitDecl.ID(id)!
      if self[id].baseName == name {
        return TraitType(id, ast: self)
      }
    }

    return nil
  }

  /// Returns the trait describing types whose instances are expressible by this literal or `nil`
  /// if it does not exist.
  ///
  /// - Requires: The Core library must have been loaded.
  public func coreTrait<T: Expr>(forTypesExpressibleBy literal: T.Type) -> TraitType? {
    switch literal.kind {
    case FloatLiteralExpr.self:
      return core.expressibleByFloatLiteral.type
    case IntegerLiteralExpr.self:
      return core.expressibleByIntegerLiteral.type
    default:
      return nil
    }
  }

  // MARK: Helpers

  /// Returns the ID of the module named `n` if such a module has been loaded, or `nil` otherwise.
  public func module(named n: String) -> ModuleDecl.ID? {
    modules.first(where: { self[$0].baseName == n })
  }

  /// Returns the top-level declarations in the lexical scope of `module`.
  private func topLevelDecls(_ module: ModuleDecl.ID) -> some Collection<AnyDeclID> {
    self[self[module].sources].map(\.decls).joined()
  }

  /// Returns the requirements declared in `t`.
  public func requirements(of t: TraitDecl.ID) -> RequirementSequence {
    .init(t, in: self)
  }

  /// Returns the requirements named `n` in `t`.
  ///
  /// If `n` is overloaded, the requirements are returned in the order in which they are declared
  /// in the source code.
  public func requirements(_ n: Name, in t: TraitDecl.ID) -> [AnyDeclID] {
    self[t].members.compactMap({ (m) -> AnyDeclID? in
      switch m.kind {
      case AssociatedValueDecl.self:
        return (n == Name(stem: self[AssociatedValueDecl.ID(m)!].baseName)) ? m : nil

      case AssociatedTypeDecl.self:
        return (n == Name(stem: self[AssociatedTypeDecl.ID(m)!].baseName)) ? m : nil

      case FunctionDecl.self:
        return (n == name(of: FunctionDecl.ID(m)!)) ? m : nil

      case InitializerDecl.self:
        return (n == name(of: InitializerDecl.ID(m)!)) ? m : nil

      case MethodDecl.self:
        let d = MethodDecl.ID(m)!
        if let i = n.introducer {
          guard n.removingIntroducer() == name(of: d) else { return nil }
          return self[d].impls
            .first(where: { self[$0].introducer.value == i })
            .map(AnyDeclID.init(_:))
        } else {
          return (name(of: d) == n) ? m : nil
        }

      case SubscriptDecl.self:
        let d = SubscriptDecl.ID(m)!
        if let i = n.introducer {
          guard n.removingIntroducer() == name(of: d) else { return nil }
          return self[d].impls
            .first(where: { self[$0].introducer.value == i })
            .map(AnyDeclID.init(_:))
        } else {
          return (name(of: d) == n) ? m : nil
        }

      default:
        return nil
      }
    })
  }

  /// Returns the kind identifying synthesized declarations of `requirement`, or `nil` if
  /// `requirement` is not synthesizable.
  public func synthesizedKind<T: DeclID>(of requirement: T) -> SynthesizedFunctionDecl.Kind? {
    switch requirement.rawValue {
    case core.deinitializable.deinitialize.rawValue:
      return .deinitialize
    case core.movable.moveInitialize.rawValue:
      return .moveInitialization
    case core.movable.moveAssign.rawValue:
      return .moveAssignment
    case core.copyable.copy.rawValue:
      return .copy
    case core.equatable.equal.rawValue:
      return .equal
    default:
      return nil
    }
  }

  /// Returns a table mapping each parameter of `d` to its default argument if `d` is a function,
  /// initializer, method or subscript declaration; otherwise, returns `nil`.
  public func defaultArguments(of d: AnyDeclID) -> [AnyExprID?]? {
    runtimeParameters(of: d)?.map({ self[$0].defaultValue })
  }

  /// Returns the name of entity defining the implementation of `d` if it is external.
  public func externalName(of d: FunctionDecl.ID) -> String? {
    self[d].attributes.first(where: { $0.value.name.value == "@external" }).map { (a) in
      if a.value.arguments[0].value.kind.value is StringLiteralExpr.Type {
        return self[StringLiteralExpr.ID(a.value.arguments[0].value)]!.value
      } else {
        unreachable()
      }
    }
  }

  /// Returns the name of the entity interfaced by the declared function if it is an FFI.
  public func foreignName(of d: FunctionDecl.ID) -> String? {
    self[d].attributes.first(where: { $0.value.name.value == "@ffi" }).map { (a) in
      if a.value.arguments[0].value.kind.value is StringLiteralExpr.Type {
        return self[StringLiteralExpr.ID(a.value.arguments[0].value)]!.value
      } else {
        unreachable()
      }
    }
  }

  /// Returns the run-time parameters of `d` iff `d` is callable.
  public func runtimeParameters(of d: AnyDeclID) -> [ParameterDecl.ID]? {
    switch d.kind {
    case FunctionDecl.self:
      return self[FunctionDecl.ID(d)!].parameters
    case InitializerDecl.self:
      return self[InitializerDecl.ID(d)!].parameters
    case MethodDecl.self:
      return self[MethodDecl.ID(d)!].parameters
    case SubscriptDecl.self:
      return self[SubscriptDecl.ID(d)!].parameters
    default:
      return nil
    }
  }

  /// Returns the generic parameters introduced by `d`.
  public func genericParameters(introducedBy d: AnyDeclID) -> [GenericParameterDecl.ID] {
    if let s = self[d] as? GenericScope {
      return s.genericParameters
    } else {
      return []
    }
  }

  /// Returns the name of `d` unless `d` is anonymous.
  public func name(of d: FunctionDecl.ID) -> Name? {
    guard let stem = self[d].identifier?.value else { return nil }
    if let notation = self[d].notation?.value {
      return .init(stem: stem, notation: notation)
    } else {
      return .init(stem: stem, labels: self[self[d].parameters].map(\.label?.value))
    }
  }

  /// Returns the name of `d`.
  public func name(of d: InitializerDecl.ID) -> Name {
    .init(stem: "init", labels: self[self[d].parameters].map(\.label?.value))
  }

  /// Returns the name of `d`.
  public func name(of d: MethodDecl.ID) -> Name {
    let stem = self[d].identifier.value
    if let notation = self[d].notation?.value {
      return .init(stem: stem, notation: notation)
    } else {
      return .init(stem: stem, labels: self[self[d].parameters].map(\.label?.value))
    }
  }

  /// Returns the name of `d`.
  public func name(of d: SubscriptDecl.ID) -> Name {
    let stem = self[d].identifier?.value ?? "[]"
    return .init(stem: stem, labels: self[self[d].parameters].map(\.label?.value))
  }

  /// Returns the subfields and pattern IDs of the named patterns contained in `p`.
  public func names<T: PatternID>(in p: T) -> [(subfield: RecordPath, pattern: NamePattern.ID)] {
    func visit(
      pattern: AnyPatternID,
      subfield: RecordPath,
      result: inout [(subfield: RecordPath, pattern: NamePattern.ID)]
    ) {
      switch pattern.kind {
      case BindingPattern.self:
        let s = self[BindingPattern.ID(pattern)!].subpattern
        visit(pattern: s, subfield: subfield, result: &result)

      case ExprPattern.self:
        break

      case NamePattern.self:
        result.append((subfield: subfield, pattern: NamePattern.ID(pattern)!))

      case OptionPattern.self:
        let n = self[OptionPattern.ID(pattern)!].name
        result.append((subfield: subfield, pattern: n))

      case TuplePattern.self:
        let x = TuplePattern.ID(pattern)!
        for i in 0..<self[x].elements.count {
          visit(pattern: self[x].elements[i].pattern, subfield: subfield + [i], result: &result)
        }

      case WildcardPattern.self:
        break

      default:
        unexpected(pattern, in: self)
      }
    }

    var result: [(subfield: RecordPath, pattern: NamePattern.ID)] = []
    visit(pattern: AnyPatternID(p), subfield: [], result: &result)
    return result
  }

  /// Returns `(head, tail)` where `head` contains the nominal components of `name` from right to
  /// left and `tail` is the non-nominal component of `name`, if any.
  ///
  /// Name expressions are rperesented as linked-list, whose elements are the components of a
  /// name in reverse order. This method splits such lists at the first non-nominal component.
  public func splitNominalComponents(of name: NameExpr.ID) -> ([NameExpr.ID], NameExpr.Domain) {
    var suffix = [name]
    while true {
      let d = self[suffix.last!].domain
      switch d {
      case .none, .implicit, .operand:
        return (suffix, d)
      case .explicit(let e):
        guard let p = NameExpr.ID(e) else { return (suffix, d) }
        suffix.append(p)
      }
    }
  }

  /// Calls `action` on each sub-pattern in `pattern` and its corresponding sub-expression in
  /// `expression`, along with the path to this sub-pattern, relative to `root`.
  ///
  /// Use this method to walk a pattern and a corresponding expression side by side and perform an
  /// action for each pair. Children of tuple patterns are visited in pre-order if and only if the
  /// corresponding expression is also a tuple. Otherwise, `action` is called on the tuple and the
  /// sub-patterns are not visited.
  ///
  /// - Requires: `expression` structurally matches `pattern`: If `pattern` and `expression` are
  ///   tuples, then they have equal lengths and labels.
  public func walking(
    pattern: AnyPatternID, expression: AnyExprID,
    at root: RecordPath = [],
    _ action: (_ subfield: RecordPath, _ subpattern: AnyPatternID, _ subexpression: AnyExprID) ->
      Void
  ) {
    switch pattern.kind {
    case BindingPattern.self:
      let p = self[BindingPattern.ID(pattern)]!.subpattern
      walking(pattern: p, expression: expression, at: root, action)

    case TuplePattern.kind:
      guard let e = TupleExpr.ID(expression) else {
        action(root, pattern, expression)
        return
      }

      let p = TuplePattern.ID(pattern)!
      for i in self[p].elements.indices {
        let a = self[p].elements[i]
        let b = self[e].elements[i]
        walking(pattern: a.pattern, expression: b.value, at: root + [i], action)
      }

    default:
      action(root, pattern, expression)
    }
  }

  /// Retutns the declaration of the implementation of `d` with effect `a`, if any.
  public func implementation<T: BundleDecl>(_ a: AccessEffect, of d: T.ID) -> T.Variant.ID? {
    self[d].impls.first(where: { (i) in self[i].introducer.value == a })
  }

  /// Returns `true` iff `s` is a consuming for-loop.
  public func isConsuming(_ s: ForStmt.ID) -> Bool {
    self[self[self[s].binding].pattern].introducer.value.isConsuming
  }

  /// Returns `true` if `e` is an expression starting with an implicit name qualification.
  public func isImplicitlyQualified(_ e: AnyExprID) -> Bool {
    switch e.kind {
    case FunctionCallExpr.self:
      return isImplicitlyQualified(self[FunctionCallExpr.ID(e)!].callee)
    case NameExpr.self:
      return isImplicitlyQualified(NameExpr.ID(e)!)
    default:
      return false
    }
  }

  /// Returns `true` if `e` is an expression starting with an implicit name qualification.
  public func isImplicitlyQualified(_ e: NameExpr.ID) -> Bool {
    switch self[e].domain {
    case .implicit:
      return true
    case .explicit(let e):
      return isImplicitlyQualified(e)
    case .none, .operand:
      return false
    }
  }

  /// Returns `true` iff `e` is an expression that's marked for mutation.
  public func isMarkedForMutation(_ e: AnyExprID) -> Bool {
    switch e.kind {
    case InoutExpr.self:
      return true
    case NameExpr.self:
      return isMarkedForMutation(NameExpr.ID(e)!)
    case SubscriptCallExpr.self:
      return isMarkedForMutation(self[SubscriptCallExpr.ID(e)!].callee)
    default:
      return false
    }
  }

  /// Returns `true` iff `e` is an expression that's marked for mutation.
  public func isMarkedForMutation(_ e: NameExpr.ID) -> Bool {
    switch self[e].domain {
    case .explicit(let n):
      return isMarkedForMutation(n)
    default:
      return false
    }
  }

  /// Returns `true` iff `e` is an expression that's marked for mutation.
  public func isMarkedForMutation(_ e: FoldedSequenceExpr) -> Bool {
    if case .leaf(let l) = e {
      return isMarkedForMutation(l)
    } else {
      return false
    }
  }

  /// Returns the source site of `expr`.
  public func site(of expr: FoldedSequenceExpr) -> SourceRange {
    switch expr {
    case .leaf(let i):
      return self[i].site

    case .infix(_, let lhs, let rhs):
      let lhsSite = site(of: lhs)
      let rhsSite = site(of: rhs)
      return lhsSite.extended(upTo: rhsSite.endIndex)
    }
  }

  /// Returns a site suitable to emit diagnostics related to `d` as a whole.
  public func siteForDiagnostics<T: DeclID>(about d: T) -> SourceRange {
    .empty(at: (introducerSite(of: d) ?? self[d].site).start)
  }

  /// Returns the site from which the introducer of `d` was parsed, if any.
  public func introducerSite<T: DeclID>(of d: T) -> SourceRange? {
    switch d.kind {
    case AssociatedTypeDecl.self:
      return self[AssociatedTypeDecl.ID(d)!].introducerSite
    case AssociatedValueDecl.self:
      return self[AssociatedValueDecl.ID(d)!].introducerSite
    case BindingDecl.self:
      return self[self[BindingDecl.ID(d)!].pattern].introducer.site
    case ConformanceDecl.self:
      return self[ConformanceDecl.ID(d)!].introducerSite
    case ExtensionDecl.self:
      return self[ExtensionDecl.ID(d)!].introducerSite
    case FunctionDecl.self:
      return self[FunctionDecl.ID(d)!].introducerSite
    case GenericParameterDecl.self:
      return nil
    case ImportDecl.self:
      return self[ImportDecl.ID(d)!].introducerSite
    case InitializerDecl.self:
      return self[InitializerDecl.ID(d)!].introducer.site
    case MethodDecl.self:
      return self[MethodDecl.ID(d)!].introducerSite
    case MethodImpl.self:
      return self[MethodImpl.ID(d)!].introducer.site
    case ModuleDecl.self:
      return nil
    case NamespaceDecl.self:
      return self[NamespaceDecl.ID(d)!].introducerSite
    case OperatorDecl.self:
      return self[OperatorDecl.ID(d)!].introducerSite
    case ParameterDecl.self:
      return nil
    case ProductTypeDecl.self:
      return self[ProductTypeDecl.ID(d)!].introducerSite
    case SubscriptDecl.self:
      return self[SubscriptDecl.ID(d)!].introducer.site
    case SubscriptImpl.self:
      return self[SubscriptImpl.ID(d)!].introducer.site
    case TraitDecl.self:
      return self[TraitDecl.ID(d)!].introducerSite
    case TypeAliasDecl.self:
      return self[TypeAliasDecl.ID(d)!].introducerSite
    default:
      return nil
    }
  }

}

extension AST: Codable {

  /// The format of data that must be injected into a `StatefulEncoder` for serializing an `AST`
  /// instance.
  typealias EncodingState = SourceFile.EncodingState

  /// The format of data that must be injected into a `StatefulDecoder` for deserializing an `AST`
  /// instance.
  typealias DecodingState = SourceFile.DecodingState

  /// The parts of an encoded AST.
  private enum CodingKeys: String, CodingKey {

    /// The main content of the AST
    case storage

    /// Separately encoded content such as `SourceFile` representations, used for reconstructing
    /// `storage`.
    case decodingState

  }

  public init(from decoder: Decoder) throws {
    let container = try decoder.container(keyedBy: CodingKeys.self)

    let decodingContext = try container.decode(DecodingState.self, forKey: .decodingState)
    decoder[state: DecodingState.self] = decodingContext
    self.storage = try container.decode(AST.Storage.self, forKey: .storage)
  }

  public func encode(to encoder: Encoder) throws {
    var container = encoder.container(keyedBy: CodingKeys.self)

    try container.encode(storage, forKey: .storage)
    let decodingState = encoder[state: EncodingState.self].decodingState()
    try container.encode(decodingState, forKey: .decodingState)

  }

}

extension StatefulEncoder {

  /// `self` prepared for encoding an `AST`.
  public var forAST: Self {
    var r = self
    r.setState(AST.EncodingState())
    return r
  }

}

extension StatefulDecoder {

  /// `self` prepared for decoding an `AST`.
  public var forAST: Self {
    var r = self
    r.setState(AST.DecodingState())
    return r
  }

}
