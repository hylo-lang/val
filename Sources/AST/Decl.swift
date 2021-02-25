import Basic

/// A node representing the declaration of one or more entities.
public protocol Decl: Node {

  /// The innermost parent in which this declaration resides.
  var parentDeclSpace: DeclSpace? { get }

  /// The (semantic) state of the declaration.
  var state: DeclState { get }

  /// Sets the state of this declaration.
  func setState(_ newState: DeclState)

  /// Accepts the given visitor.
  ///
  /// - Parameter visitor: A declaration visitor.
  func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor

}

/// The state of a declaration, as it goes through type checking.
public enum DeclState: Int, Comparable {

  /// The declaration was just parsed; no semantic information is available.
  case parsed

  /// The type of the declaration has been requested and is being realized.
  case realizationRequested

  /// The type of the declaration is available for type inference, but the declaration has not been
  /// type checked yet.
  ///
  /// For a `TypeDecl` or a `ValueDecl`, the `type` property of the declaration has been realized.
  /// For a `TypeExtDec`, the extension has been bound.
  case realized

  /// The declaration has been scheduled for type checking. Any attempt to transition back to this
  /// state should be interpreted as a circular dependency.
  case typeCheckRequested

  /// Type checking has been completed; the declaration is semantically well-formed.
  case typeChecked

  /// The declaration has been found to be ill-formed; it should be ignored by all subsequent
  /// semantic analysis phases, without producing any further diagnostic.
  ///
  /// - Note: `invalid` must have the largest raw value, so that `.invalid < validState` always
  ///   answer `false` for any arbitrary valid state.
  case invalid

  /// Returns a Boolean value indicating whether one state is more "advanced" than the other.
  public static func < (lhs: DeclState, rhs: DeclState) -> Bool {
    return lhs.rawValue < rhs.rawValue
  }

}

/// A type or a value declaration.
public protocol TypeOrValueDecl: Decl {

  /// The name of the declaration.
  var name: String { get }

  /// The semantic type of the declaration, outside of its generic context.
  var type: ValType { get }

  /// A flag indicating whether the declaration is overloadable.
  var isOverloadable: Bool { get }

}

/// A type declaration.
public protocol TypeDecl: TypeOrValueDecl, DeclSpace {

  /// The (unbound) type of instances of the declared type.
  ///
  /// For the type of the declaration itself, use `type`, which returns a kind.
  var instanceType: ValType { get }

}

extension TypeDecl {

  public var instanceType: ValType {
    return (type as! KindType).type
  }

}

/// A named declaration.
public protocol ValueDecl: TypeOrValueDecl {

  /// A flag indicating whether the declaration describes the member of a type.
  var isMember: Bool { get }

  /// The type of the declaration.
  var type: ValType { get set }

  /// Realizes the semantic type of the value being declared.
  func realize() -> ValType

}

extension ValueDecl {

  /// Contextualize the type of this declaration from the given use site.
  ///
  /// - Parameters:
  ///   - useSite: The declaration space from which the declaration is being referred.
  ///   - args: A dictionary containing specialization arguments for generic type parameters.
  ///   - handleConstraint: A closure that accepts contextualized contraint prototypes. It is
  ///     called only if the contextualized type contains opened generic types for which there
  ///     exist type requirements.
  public func contextualize(
    from useSite: DeclSpace,
    args: [GenericParamType: ValType] = [:],
    processingContraintsWith handleConstraint: (GenericEnv.ConstraintPrototype) -> Void = { _ in }
  ) -> ValType {
    // Realize the declaration's type.
    var genericType = realize()

    // Specialize the generic parameters for which arguments have been provided.
    if !args.isEmpty {
      genericType = genericType.specialized(with: args)
    }

    guard genericType.hasTypeParams else { return genericType }

    // If the declaration is its own generic environment, then we must contextualize it externally,
    // regardless of the use-site. This situation corresponds to a "fresh" use of a generic
    // declaration within its own space (e.g., a recursive call to a generic function).
    if let gds = self as? GenericDeclSpace {
      guard let env = gds.prepareGenericEnv() else {
        return type.context.errorType
      }

      // Adjust the use site depending on the type of declaration.
      var adjustedSite: DeclSpace
      if gds is CtorDecl {
        // Constructors are contextualized from outside of their type declaration.
        adjustedSite = gds.spacesUpToRoot.first(where: { $0 is TypeDecl })!.parentDeclSpace!
      } else {
        adjustedSite = gds
      }
      if adjustedSite.isDescendant(of: useSite) {
        adjustedSite = useSite
      }

      return env.contextualize(
        genericType, from: adjustedSite, processingContraintsWith: handleConstraint)
    }

    // Find the innermost generic space, relative to this declaration. We can assume there's one,
    // otherwise `realize()` would have failed to resolve the decl.
    guard let env = parentDeclSpace!.innermostGenericSpace!.prepareGenericEnv() else {
      return type.context.errorType
    }
    return env.contextualize(
      genericType, from: useSite, processingContraintsWith: handleConstraint)
  }

}

/// A declaration that consists of a pattern and an optional initializer for the variables declared
/// in this pattern.
public final class PatternBindingDecl: Decl {

  public init(
    isMutable       : Bool,
    pattern         : Pattern,
    typeSign        : TypeRepr?,
    initializer     : Expr?,
    declKeywordRange: SourceRange,
    range           : SourceRange
  ) {
    self.isMutable = isMutable
    self.pattern = pattern
    self.sign = typeSign
    self.initializer = initializer
    self.declKeywordRange = declKeywordRange
    self.range = range
  }

  /// A flag indicating whether the declared variables are mutable.
  public var isMutable: Bool

  /// A flag indicating whether the declaration describes member variables.
  public var isMember: Bool {
    return (parentDeclSpace is NominalTypeDecl || parentDeclSpace is TypeExtDecl)
  }

  /// The pattern being bound.
  public var pattern: Pattern

  /// The signature of the pattern.
  public var sign: TypeRepr?

  /// The initializer for the variables declared by the pattern.
  public var initializer: Expr?

  /// The source range of this declaration `val` or `var` keyword.
  public var declKeywordRange: SourceRange

  public var range: SourceRange

  public weak var parentDeclSpace: DeclSpace?

  public private(set) var state = DeclState.parsed

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  /// The declaration of all variables declared in this pattern.
  public var varDecls: [VarDecl] = []

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A variable declaration.
public final class VarDecl: ValueDecl {

  public init(name: String, type: ValType, range: SourceRange) {
    self.name = name
    self.type = type
    self.range = range
  }

  public var name: String

  /// The pattern binding declaration that introduces this variable declaration.
  public weak var patternBindingDecl: PatternBindingDecl?

  public var range: SourceRange

  /// The backend of the variable.
  public var backend: VarBackend = .storage

  /// A flag indicating whether the variable has storage.
  public var hasStorage: Bool { backend == .storage }

  /// A flag indicating whether the variable is mutable.
  public var isMutable: Bool { patternBindingDecl?.isMutable ?? false }

  /// A flag indicating whether the variable is member of a pattern binding declared as a member.
  public var isMember: Bool { patternBindingDecl?.isMember ?? false }

  public var isOverloadable: Bool { false }

  public weak var parentDeclSpace: DeclSpace?

  public private(set) var state = DeclState.parsed

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  public var type: ValType

  public func realize() -> ValType {
    if state >= .realized { return type }

    // Variable declarations can't realize on their own. Their type is defined when the enclosing
    // pattern binding declaration is type checked.
    preconditionFailure("variable declarations can't realize on their own")
  }

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// The "backend" of a variable declaration, describing how its value is stored and retrieved.
///
/// In the future, we may use this enum to represent computed and lazy properties.
public enum VarBackend {

  /// The value of the variable is stored in memory.
  case storage

}

/// The base class for function declarations.
public class BaseFunDecl: ValueDecl, GenericDeclSpace {

  public init(
    name          : String,
    declModifiers : [DeclModifier] = [],
    genericClause : GenericClause? = nil,
    params        : [FunParamDecl] = [],
    retTypeSign   : TypeRepr?      = nil,
    body          : BraceStmt?     = nil,
    type          : ValType,
    range         : SourceRange
  ) {
    self.name = name
    self.declModifiers = declModifiers
    self.genericClause = genericClause
    self.params = params
    self.retSign = retTypeSign
    self.body = body
    self.type = type
    self.range = range

    // Process the function modifiers.
    self.props = FunDeclProps()
    for modifier in declModifiers {
      switch modifier.kind {
      case .mut   : props.formUnion(.isMutating)
      case .static: props.formUnion(.isStatic)
      default     : continue
      }
    }
  }

  // MARK: Source properties

  /// The name of the function (empty for anonymous functions).
  public var name: String

  /// The local discriminator for the function.
  ///
  /// This is the index of the function in the sequence of anonymous declarations in the parent
  /// declaration space.
  public var discriminator = 0

  /// The semantic properties of the declaration.
  public var props: FunDeclProps

  /// Indicates whether the function is a member of a type.
  ///
  /// - Note: Constructors are *not* considered to be member functions.
  public var isMember: Bool { props.contains(.isMember) }

  /// Indicates whether the function is mutating its receiver.
  public var isMutating: Bool { props.contains(.isMutating) }

  /// Indicates whether the function is static.
  public var isStatic: Bool { props.contains(.isStatic) }

  /// Indicates whether the function is built-in.
  public var isBuiltin: Bool { props.contains(.isBuiltin) }

  /// The declaration modifiers of the function.
  ///
  /// This array only contains the declaration modifiers as found in source. It may not accurately
  /// describe the relevant bits in `props`, nor vice-versa.
  public var declModifiers: [DeclModifier]

  /// The generic clause of the declaration.
  public var genericClause: GenericClause?

  /// The parameters of the function.
  public var params: [FunParamDecl]

  /// The signature of the function's return type.
  public var retSign: TypeRepr?

  /// The body of the function.
  public var body: BraceStmt?

  public var range: SourceRange

  // MARK: Implicit declarations

  /// The implicit declaration of the `self` parameter for member functions.
  ///
  /// - Note: Accessing this property will trap if the function declaration is in an extension that
  ///   hasn't been bound to a nominal type yet.
  public private(set) lazy var selfDecl: FunParamDecl? = {
    guard isMember || (self is CtorDecl) else { return nil }

    let receiverType: ValType
    switch parentDeclSpace {
    case let typeDecl as NominalTypeDecl:
      // The function is declared in the body of a nominal type.
      receiverType = typeDecl.receiverType

    case let extnDecl as TypeExtDecl:
      // The function is declared in the body of a type extension.
      guard let typeDecl = extnDecl.extendedDecl else {
        let decl = FunParamDecl(
          name: "self", externalName: "self", type: type.context.errorType, range: .invalid)
        decl.setState(.invalid)
        return decl
      }
      receiverType = typeDecl.receiverType

    default:
      fatalError("unreachable")
    }

    let decl = FunParamDecl(
      name: "self", externalName: "self",
      type: isMutating
        ? type.context.inoutType(of: receiverType)
        : receiverType,
      range: .invalid)
    decl.parentDeclSpace = self
    decl.setState(.typeChecked)
    return decl
  }()

  // MARK: Name Lookup

  public weak var parentDeclSpace: DeclSpace?

  public var isOverloadable: Bool { true }

  /// Looks up for declarations that match the given name, directly enclosed within the function
  /// declaration space.
  ///
  /// The returned type declarations are the function's generic parameters. The value declarations
  /// are its explicit and implicit parameters. The declarations scoped within the function's body
  /// are **not** included in either of these sets. Those reside in a nested space.
  public func lookup(qualified name: String) -> LookupResult {
    let types  = genericClause.map({ clause in clause.params.filter({ $0.name == name }) }) ?? []
    var values = params.filter({ $0.name == name })
    if name == "self", let selfDecl = self.selfDecl {
      values.append(selfDecl)
    }

    return LookupResult(types: types, values: values)
  }

  // MARK: Semantic properties

  public private(set) var state = DeclState.parsed

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    assert((newState != .typeCheckRequested) || (state >= .realized),
           "type checking requested before the function signature was realized")

    state = newState
  }

  /// The "applied" type of the function.
  ///
  /// This property must be kept synchronized with the function type implicitly described by the
  /// parameter list and return signature. Setting its value directly is discouraged, you should
  /// use `realize()` instead.
  ///
  /// - Note: Member functions accept the receiver (i.e., `self`) as an implicit first parameter.
  ///   This means that a call to a method `T -> U` is actually an application of an *unapplied*
  ///   function `(Self, T) -> U`, where `Self` is the receiver's type. This property denotes the
  ///   *applied* type, which should be understood as the return type the unapplied function's
  ///   partial application.
  public var type: ValType

  /// The "unapplied" type of the function.
  ///
  /// For member functions, this is the type of the function extended with an implicit receiver
  /// parameter. For other functions, this is equal to `type`.
  public var unappliedType: ValType {
    guard isMember else { return type }

    let funType = type as! FunType
    var paramTypeElems = (funType.paramType as? TupleType)?.elems
      ?? [TupleType.Elem(type: funType.paramType)]
    paramTypeElems.insert(TupleType.Elem(label: "self", type: selfDecl!.type), at: 0)

    return type.context.funType(
      paramType: type.context.tupleType(paramTypeElems),
      retType: funType.retType)
  }

  /// Realizes the "applied" type of the function from its signature.
  ///
  /// For member functions, this is the type of the function extended with an implicit receiver
  /// parameter. For other functions, this is equal to `type`.
  public func realize() -> ValType {
    if state >= .realized { return type }

    // Realize the parameters.
    var paramTypeElems: [TupleType.Elem] = []
    for param in params {
      _ = param.realize()
      paramTypeElems.append(TupleType.Elem(label: param.externalName, type: param.type))
    }
    let paramType = type.context.tupleType(paramTypeElems)

    // Realize the return type.
    let retType: ValType
    if let sign = retSign {
      retType = sign.realize(unqualifiedFrom: self)
    } else {
      retType = type.context.unitType
    }

    type = type.context.funType(paramType: paramType, retType: retType)
    setState(.realized)
    return type
  }

  public var hasOwnGenericParams: Bool { genericClause != nil }

  public var genericEnv: GenericEnv?

  public func prepareGenericEnv() -> GenericEnv? {
    if let env = genericEnv { return env }

    if let clause = genericClause {
      genericEnv = GenericEnv(
        space: self,
        params: clause.params.map({ $0.instanceType as! GenericParamType }),
        typeReqs: clause.typeReqs,
        context: type.context)
      guard genericEnv != nil else {
        setState(.invalid)
        return nil
      }
    } else {
      genericEnv = GenericEnv(space: self)
    }

    return genericEnv
  }

  // MARK: Misc.

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

  /// A set representing various properties of a function declaration.
  public struct FunDeclProps: OptionSet {

    public init(rawValue: Int) {
      self.rawValue = rawValue
    }

    public let rawValue: Int

    public static let isMember   = FunDeclProps(rawValue: 1 << 0)
    public static let isMutating = FunDeclProps(rawValue: 1 << 1)
    public static let isStatic   = FunDeclProps(rawValue: 1 << 2)
    public static let isBuiltin  = FunDeclProps(rawValue: 1 << 3)

  }

}

/// A function declaration.
public final class FunDecl: BaseFunDecl {

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A constructor declaration.
public final class CtorDecl: BaseFunDecl {

  public init(
    declModifiers : [DeclModifier] = [],
    genericClause : GenericClause? = nil,
    params        : [FunParamDecl] = [],
    body          : BraceStmt?     = nil,
    type          : ValType,
    range         : SourceRange
  ) {
    super.init(
      name: "new",
      declModifiers: declModifiers,
      genericClause: genericClause,
      params: params,
      body: body,
      type: type,
      range: range)
    props.insert(.isMutating)
  }

  public override func realize() -> ValType {
    if state >= .realized { return type }

    var paramTypeElems: [TupleType.Elem] = []
    for param in params {
      _ = param.realize()
      paramTypeElems.append(TupleType.Elem(label: param.externalName, type: param.type))
    }
    let paramType = type.context.tupleType(paramTypeElems)
    let retType = (selfDecl!.type as! InoutType).base

    type = type.context.funType(paramType: paramType, retType: retType)
    setState(.realized)
    return type
  }

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// The declaration of a function parameter.
public final class FunParamDecl: ValueDecl {

  public init(
    name        : String,
    externalName: String?   = nil,
    typeSign    : TypeRepr? = nil,
    type        : ValType,
    range       : SourceRange
  ) {
    self.name = name
    self.externalName = externalName
    self.sign = typeSign
    self.type = type
    self.range = range
  }

  /// The internal name of the parameter.
  public var name: String

  /// The external name of the parameter.
  public var externalName: String?

  /// The signature of the parameter's type.
  public var sign: TypeRepr?

  public var range: SourceRange

  public weak var parentDeclSpace: DeclSpace?

  public var isMember: Bool { false }

  public var isOverloadable: Bool { false }

  public private(set) var state = DeclState.parsed

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  public var type: ValType

  public func realize() -> ValType {
    if state >= .realized { return type }

    if let sign = self.sign {
      type = sign.realize(unqualifiedFrom: parentDeclSpace!)
    } else {
      preconditionFailure("cannot realize parameter declaration without a signature")
    }

    setState(.realized)
    return type
  }

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A type declaration that can have explicit or implicit generic parameters.
public class GenericTypeDecl: TypeDecl, GenericDeclSpace {

  fileprivate init(name: String, type: ValType, range: SourceRange, state: DeclState) {
    self.name = name
    self.type = type
    self.range = range
    self.state = state
  }

  /// The name of the type.
  public var name: String = ""

  /// The generic clause of the declaration, if any.
  public var genericClause: GenericClause?

  /// The generic environment described by the type.
  public var genericEnv: GenericEnv?

  /// The views to which the type should conform.
  public var inheritances: [TypeRepr] = []

  /// The resolved type of the declaration.
  ///
  /// - Important: This should only be set at the time of the node's creation.
  public var type: ValType

  public weak var parentDeclSpace: DeclSpace?

  public private(set) var state: DeclState

  /// The internal cache backing `valueMemberTable`.
  private var _valueMemberTable: [String: [ValueDecl]]?

  /// The internal cache backing `typeMemberTable`.
  private var _typeMemberTable: [String: TypeDecl]?

  /// The internal cache backing `conformanceTable`.
  private var _conformanceTable: ConformanceLookupTable?

  public var range: SourceRange

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

  // MARK: Name lookup

  public var isOverloadable: Bool { false }

  /// A lookup table keeping track of value members.
  public var valueMemberTable: [String: [ValueDecl]] {
    updateMemberTables()
    return _valueMemberTable!
  }

  /// A lookup table keeping track of type members.
  public var typeMemberTable: [String: TypeDecl] {
    updateMemberTables()
    return _typeMemberTable!
  }

  public func lookup(qualified name: String) -> LookupResult {
    updateMemberTables()
    return LookupResult(
      types : _typeMemberTable![name].map({ [$0] }) ?? [],
      values: _valueMemberTable![name] ?? [])
  }

  // Updates or initializes the member lookup tables.
  public func updateMemberTables() {
    guard _valueMemberTable == nil else { return }

    // Initialize type lookup tables.
    _valueMemberTable = [:]
    _typeMemberTable  = [:]

    // Populate the lookup table with generic parameters.
    if let clause = genericClause {
      fill(members: clause.params)
    }

    // Populate the lookup table with explicit members.
    fill(members: explicitMembers())

    // Populate the lookup table with members declared in extensions.
    for module in type.context.modules.values {
      for extDecl in extensions(in: module) {
        fill(members: extDecl.members)
      }
    }

    // Populate the lookup table with members inherited by conformance.
    updateConformanceTable()
    for conformance in _conformanceTable!.values {
      fill(members: conformance.viewDecl.allTypeAndValueMembers.lazy.map({ $0.decl }))
    }
  }

  /// Returns the declarations of each "explicit" member in the type.
  fileprivate func explicitMembers() -> [Decl] {
    return []
  }

  /// Returns the extensions of the declaration in the given module.
  fileprivate func extensions(in module: ModuleDecl) -> [TypeExtDecl] {
    return module.extensions(of: self)
  }

  /// Fills the member lookup table with the given declarations.
  private func fill<S>(members: S) where S: Sequence, S.Element == Decl {
    for decl in members where decl.state != .invalid {
      switch decl {
      case let valueDecl as ValueDecl:
        _valueMemberTable![valueDecl.name, default: []].append(valueDecl)

      case let pbDecl as PatternBindingDecl:
        for pattern in pbDecl.pattern.namedPatterns {
          _valueMemberTable![pattern.decl.name, default: []].append(pattern.decl)
        }

      case let typeDecl as TypeDecl:
        // Check for invalid redeclarations.
        // FIXME: Shadow abstract type declarations inherited by conformance.
        guard _typeMemberTable![typeDecl.name] == nil else {
          type.context.report(
            .duplicateDeclaration(symbol: typeDecl.name, range: typeDecl.range))
          typeDecl.setState(.invalid)
          continue
        }

        _typeMemberTable![typeDecl.name] = typeDecl

      default:
        continue
      }
    }
  }

  /// A sequence with all members in this type.
  public var allTypeAndValueMembers: MemberIterator {
    updateMemberTables()
    return MemberIterator(decl: self)
  }

  /// An iterator over all the member declarations of a type.
  public struct MemberIterator: IteratorProtocol, Sequence {

    public typealias Element = (name: String, decl: TypeOrValueDecl)

    fileprivate init(decl: GenericTypeDecl) {
      self.decl = decl
      self.valueMemberIndex = (decl._valueMemberTable!.startIndex, 0)
      self.typeMemberIndex = decl._typeMemberTable!.startIndex
    }

    fileprivate unowned let decl: GenericTypeDecl

    fileprivate var valueMemberIndex: (Dictionary<String, [ValueDecl]>.Index, Int)

    fileprivate var typeMemberIndex: Dictionary<String, TypeDecl>.Index

    public mutating func next() -> (name: String, decl: TypeOrValueDecl)? {
      // Iterate over value members.
      let valueTable = decl._valueMemberTable!
      if valueMemberIndex.0 < valueTable.endIndex {
        // Extract the next member.
        let (name, bucket) = valueTable[valueMemberIndex.0]
        let member = bucket[valueMemberIndex.1]

        // Update the value member index.
        let i = valueMemberIndex.1 + 1
        valueMemberIndex = (i >= bucket.endIndex)
          ? (valueTable.index(after: valueMemberIndex.0), 0)
          : (valueMemberIndex.0, i)

        return (name, member)
      }

      // Iterate over type members.
      let typeTable = decl._typeMemberTable!
      if typeMemberIndex < typeTable.endIndex {
        let (name, member) = typeTable[typeMemberIndex]
        typeMemberIndex = typeTable.index(after: typeMemberIndex)
        return (name, member)
      }

      // We reached the end of the sequence.
      return nil
    }

  }

  // MARK: Generic parameters

  public var hasOwnGenericParams: Bool { false }

  public func prepareGenericEnv() -> GenericEnv? {
    fatalError("unreachable")
  }

  // MARK: View conformance

  /// A lookup table keeping track of the views to which the declared type conforms.
  public var conformanceTable: ConformanceLookupTable {
    get {
      updateConformanceTable()
      return _conformanceTable!
    }
    set { _conformanceTable = newValue }
  }

  // Updates or initializes the conformance lookup table.
  public func updateConformanceTable() {
    if _conformanceTable == nil {
      _conformanceTable = ConformanceLookupTable()
      for repr in inheritances {
        let reprType = repr.realize(unqualifiedFrom: parentDeclSpace!)
        if let viewType = reprType as? ViewType {
          _conformanceTable![viewType] = ViewConformance(
            viewDecl: viewType.decl as! ViewTypeDecl, range: repr.range)
        }
      }

      // FIXME: Insert inherited conformance.
      // FIXME: Insert conformance declared in extensions.
    }
  }

  /// Returns whether the declared type conforms to the given view.
  ///
  /// - Parameter viewType: A view.
  ///
  /// - Returns: `true` if there exists a type checked conformance between the declared type and
  ///   the given view. Otherwise, returns `false`.
  public func conforms(to viewType: ViewType) -> Bool {
    updateConformanceTable()
    guard let conformance = _conformanceTable![viewType] else { return false }
    return conformance.state == .checked
  }

  // MARK: Semantic properties

  /// The uncontextualized type of a reference to `self` within the context of this type.
  public var receiverType: ValType { fatalError("unreachable") }

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  // MARK: Memory layout

  /// The list of properties that have storage in this type.
  public var storedVarDecls: [VarDecl] { [] }

}

/// The base class for nominal type declarations.
public class NominalTypeDecl: GenericTypeDecl {

  public init(name: String, type: ValType, range: SourceRange) {
    super.init(name: name, type: type, range: range, state: .realized)
  }

  /// The member declarations of the type.
  ///
  /// This is the list of explicit declarations found directly within the type declaration. Use
  /// `allTypeAndValueMembers` to enumerate all member declarations, including those that are
  /// declared in extensions, inherited by conformance or synthetized.
  public var members: [Decl] = []

  fileprivate override func explicitMembers() -> [Decl] {
    return members
  }

  /// The list of properties that have storage in this type.
  public override var storedVarDecls: [VarDecl] {
    var result: [VarDecl] = []
    for case let pbDecl as PatternBindingDecl in members {
      // FIXME: Filter out computed properties.
      result.append(contentsOf: pbDecl.varDecls)
    }
    return result
  }

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A product type declaration.
public final class ProductTypeDecl: NominalTypeDecl {

  public override var hasOwnGenericParams: Bool { genericClause != nil }

  public override func prepareGenericEnv() -> GenericEnv? {
    if let env = genericEnv { return env }

    if let clause = genericClause {
      genericEnv = GenericEnv(
        space: self,
        params: clause.params.map({ $0.instanceType as! GenericParamType }),
        typeReqs: clause.typeReqs,
        context: type.context)
      guard genericEnv != nil else {
        setState(.invalid)
        return nil
      }
    } else {
      genericEnv = GenericEnv(space: self)
    }

    return genericEnv
  }

  /// The uncontextualized type of a reference to `self` within the context of this type.
  ///
  /// If the type declaration introduces its own generic type parameters, this wraps `instanceType`
  /// within a `BoundGenericType` where each parameter is bound to itself. Otherwise, this is the
  /// same as `instanceType`.
  public override var receiverType: ValType {
    if let clause = genericClause {
      // The instance type is generic (e.g., `Foo<Bar>`).
      return type.context.boundGenericType(
        decl: self,
        args: clause.params.map({ $0.instanceType }))
    } else {
      return instanceType
    }
  }

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A view type declaration.
public final class ViewTypeDecl: NominalTypeDecl {

  public override var hasOwnGenericParams: Bool { true }

  /// The implicit declaration of the `Self` generic type parameter.
  public lazy var selfTypeDecl: GenericParamDecl = {
    let paramDecl = GenericParamDecl(
      name: "Self",
      type: type.context.unresolvedType,
      range: range.lowerBound ..< range.lowerBound)

    paramDecl.parentDeclSpace = self
    paramDecl.type = type.context.genericParamType(decl: paramDecl).kind
    paramDecl.setState(.typeChecked)

    return paramDecl
  }()

  /// The uncontextualized type of a reference to `self` within the context of this type.
  public override var receiverType: ValType { selfTypeDecl.instanceType }

  /// Prepares the generic environment.
  ///
  /// View declarations delimit a generic space with a unique type parameter `Self`, which denotes
  /// conforming types existentially. `Self` is declared implicitly in a generic clause of the form
  /// `<Self where Self: V>`, where `V` is the name of the declared view.
  public override func prepareGenericEnv() -> GenericEnv? {
    if let env = genericEnv { return env }

    let selfType = selfTypeDecl.instanceType as! GenericParamType

    // Create the view's generic type requirements (i.e., `Self: V`).
    let range = self.range.lowerBound ..< self.range.lowerBound
    let req = TypeReq(
      kind: .conformance,
      lhs: UnqualTypeRepr(name: "Self", type: selfType, range: range),
      rhs: UnqualTypeRepr(name: name, type: instanceType, range: range),
      range: range)

    // Create and return the view's generic environment.
    genericEnv = GenericEnv(
      space: self, params: [selfType], typeReqs: [req], context: type.context)
    return genericEnv
  }

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A type alias declaration.
///
/// An alias declaration denotes either a "true" alias, or a type definition. The former merely
/// introduces a synonym for an existing nominal type (e.g., `type Num = Int`), while the latter
/// gives a name to a type expression (e.g., `type Handler = Event -> Unit`).
public final class AliasTypeDecl: GenericTypeDecl {

  public init(name: String, aliasedSign: TypeRepr, type: ValType, range: SourceRange) {
    self.aliasedSign = aliasedSign
    super.init(name: name, type: type, range: range, state: .parsed)
  }

  /// The signature of the aliased type.
  public var aliasedSign: TypeRepr

  /// If the declaration is a "true" type alias, the aliased declaration. Otherwise, `nil`.
  public var aliasedDecl: GenericTypeDecl? {
    switch realize() {
    case let type as NominalType:
      return type.decl
    case let type as BoundGenericType:
      return type.decl

    default:
      return nil
    }
  }

  /// The uncontextualized type of a reference to `self` within the context of this type.
  ///
  /// If the type declaration introduces its own generic type parameters, this wraps `instanceType`
  /// within a `BoundGenericType` where each parameter is bound to itself. Otherwise, this is the
  /// same as `instanceType`.
  public override var receiverType: ValType {
    if let clause = genericClause {
      // The instance type is generic (e.g., `Foo<Bar>`).
      return type.context.boundGenericType(
        decl: self,
        args: clause.params.map({ $0.instanceType }))
    } else {
      return instanceType
    }
  }

  /// Realizes the semantic type denoted by the declaration.
  public func realize() -> ValType {
    guard state < .realized else { return type }
    setState(.realizationRequested)

    // Realize the aliased signature.
    let aliasedType = aliasedSign.realize(unqualifiedFrom: parentDeclSpace!)
    type = aliasedType.kind
    guard !aliasedType.hasErrors else {
      setState(.invalid)
      return type
    }

    /// Complain if the signature references the declaration itself.
    // FIXME

    // Complain if the aliased signature describes an in-out type.
    if type is InoutType {
      type.context.report(.invalidMutatingTypeModifier(range: aliasedSign.range))
      setState(.invalid)
      return type
    }

    // If the aliased type is a single generic type, complain if the alias declares additional
    // view conformances. These should be expressed with an extension.
    if !inheritances.isEmpty && (aliasedType is NominalType) {
      type.context.report(.newConformanceOnNominalTypeAlias(range: inheritances[0].range))
    }

    return type
  }

  public override func lookup(qualified name: String) -> LookupResult {
    // Name lookups require the declaration to be realized, so that we can search into possible
    // extensions. However, realizing the aliased signature will trigger name lookups into this
    // declaration, causing infinite recursion. That's because the signature's identifiers may
    // refer to generic parameters. To break the cycle, we should restrict the search space to
    // to the generic clause until the declaration is fully realized. This is fine, because the
    // types referred by the aliased signature can't be declared within the aliased type.
    if state == .realizationRequested {
      guard let param = genericClause?.params.first(where: { $0.name == name }) else {
        return LookupResult()
      }
      return LookupResult(types: [param], values: [])
    }

    // Realize the aliased signature.
    _ = realize()
    guard state >= .realized else { return LookupResult() }

    // Search within the declaration and its conformances.
    var results = super.lookup(qualified: name)

    // Complete the results with the members of the declared type.
    let aliasedResults = aliasedSign.type.lookup(member: name)
    results.append(contentsOf: aliasedResults)

    return results
  }

  fileprivate override func extensions(in module: ModuleDecl) -> [TypeExtDecl] {
    if let decl = aliasedDecl {
      return decl.extensions(in: module)
    } else {
      return module.extensions(of: self)
    }
  }

  public override func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// The declaration of a generic parameter.
public final class GenericParamDecl: TypeDecl {

  public init(name: String, type: ValType, range: SourceRange) {
    self.name = name
    self.type = type
    self.range = range
  }

  public var name: String

  public var range: SourceRange

  public weak var parentDeclSpace: DeclSpace?

  public var isOverloadable: Bool { false }

  public func lookup(qualified name: String) -> LookupResult {
    return LookupResult()
  }

  public private(set) var state = DeclState.realized

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  public var type: ValType

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}

/// A type extension declaration.
///
/// This is not a `TypeDecl`, as it does not define any type. An extension merely represents a set
/// of declarations that should be "added" to a type.
public final class TypeExtDecl: Decl, DeclSpace {

  public init(extendedIdent: IdentTypeRepr, members: [Decl], range: SourceRange) {
    self.extendedIdent = extendedIdent
    self.members = members
    self.range = range
  }

  /// The identifier of the type being extended.
  public var extendedIdent: IdentTypeRepr

  /// The member declarations of the type.
  public var members: [Decl]

  public var range: SourceRange

  // MARK: Name lookup

  /// The innermost parent in which this declaration resides.
  ///
  /// This refers to the declaration space in which the extension was parsed until it is bound.
  /// Then, this refers to the extended declaration, virtually nesting the extension within the
  /// the declaration space of the type it extends.
  public weak var parentDeclSpace: DeclSpace?

  public func lookup(qualified name: String) -> LookupResult {
    // Bind the extension and forward the lookup to the extended type.
    return computeExtendedDecl()?.lookup(qualified: name) ?? LookupResult()
  }

  // MARK: Semantic properties

  public private(set) var state = DeclState.parsed

  public func setState(_ newState: DeclState) {
    assert(newState >= state)
    state = newState
  }

  /// The declaration of the extended type.
  public var extendedDecl: GenericTypeDecl? {
    return computeExtendedDecl()
  }

  /// The underlying storage for `extendedDecl`.
  private var _extendedDecl: NominalTypeDecl?

  /// Computes the declaration that is extended by this extension.
  public func computeExtendedDecl() -> GenericTypeDecl? {
    guard state != .invalid else { return nil }
    if state >= .realized {
      return _extendedDecl
    }

    let type = extendedIdent.realize(unqualifiedFrom: parentDeclSpace!)
    guard !(type is ErrorType) else {
      // The diagnostic is emitted by the failed attempt to realize the base.
      state = .invalid
      return nil
    }

    guard let decl = (type as? NominalType)?.decl else {
      type.context.report(.nonNominalExtension(type, range: extendedIdent.range))
      state = .invalid
      return nil
    }

    parentDeclSpace = decl
    state = .realized
    return decl
  }

  public func accept<V>(_ visitor: V) -> V.DeclResult where V: DeclVisitor {
    return visitor.visit(self)
  }

}
