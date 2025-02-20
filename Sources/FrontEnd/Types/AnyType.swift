import OrderedCollections
import Utils

/// A box wrapping a type.
private protocol TypeBox {

  /// Hashes the salient parts of the wrapped value into `hasher`.
  func hash(into hasher: inout Hasher)

  /// Returns whether the value wrapped inside `self` is equal to that wrapped inside `other`.
  func equals<Other: TypeBox>(_ other: Other) -> Bool

  /// Returns the value wrapped inside `self` with its type erased.
  func unwrap() -> any TypeProtocol

  /// Returns the value wrapped inside `self` as an instance of `T` or `nil` if that value has a
  /// different type.
  func unwrap<T: TypeProtocol>(as: T.Type) -> T?

  /// Applies `TypeProtocol.transform(mutating:_:)` on `m` and the types that are part of `self`.
  func transformParts<M>(
    mutating m: inout M, _ transformer: (inout M, AnyType) -> TypeTransformAction
  ) -> any TypeProtocol

}

/// A box wrapping an instance of `Base`.
private struct ConcreteTypeBox<Base: TypeProtocol>: TypeBox {

  /// The value wrapped by this instance.
  let base: Base

  func hash(into hasher: inout Hasher) {
    base.hash(into: &hasher)
  }

  func equals<Other: TypeBox>(_ other: Other) -> Bool {
    base == other.unwrap(as: Base.self)
  }

  func unwrap() -> any TypeProtocol {
    base
  }

  func unwrap<T: TypeProtocol>(as: T.Type) -> T? {
    base as? T
  }

  /// Applies `TypeProtocol.transform(mutating:_:)` on `m` and the types that are part of `self`.
  func transformParts<M>(
    mutating m: inout M, _ transformer: (inout M, AnyType) -> TypeTransformAction
  ) -> any TypeProtocol {
    base.transformParts(mutating: &m, transformer)
  }

}

/// The (static) type of an entity.
public struct AnyType {

  /// Hylo's `Any` type.
  public static let any = ^ExistentialType(traits: [], constraints: [])

  /// Hylo's `Never` type.
  public static let never = ^UnionType([])

  /// Hylo's `Void` type.
  public static let void = ^TupleType([])

  /// A shorthand for `^ErrorType()`.
  public static let error = ^ErrorType()

  /// Returns the given built-in type symbol wrapped in a type-erased container.
  public static func builtin(_ type: BuiltinType) -> AnyType { ^type }

  /// The value wrapped by this instance.
  private var wrapped: TypeBox

  /// Creates a type-erased container wrapping the given instance.
  ///
  /// - Parameter base: A type to wrap.
  public init<T: TypeProtocol>(_ base: T) {
    if let t = base as? AnyType {
      self.wrapped = t.wrapped
    } else {
      self.wrapped = ConcreteTypeBox(base: base)
    }
  }

  /// Accesses value wrapped by this instance.
  ///
  /// The `base` property can be cast back to its original type using one of the type casting
  /// operators (`as?`, `as!`, or `as`).
  public var base: any TypeProtocol {
    wrapped.unwrap()
  }

  /// `self` if `!self[.hasError]`; otherwise, `nil`.
  public var errorFree: AnyType? {
    self[.hasError] ? nil : self
  }

  /// `self` transformed as the type of a member of `receiver`, which is existential.
  public func asMember(of receiver: ExistentialType) -> AnyType {
    let m = ArrowType(self) ?? UNIMPLEMENTED()
    return ^m.asMember(of: receiver)
  }

  /// Returns the generic arguments specializing `self`.
  public var specialization: GenericArguments {
    switch base {
    case let u as BoundGenericType:
      return .init(u)
    case let u as TypeAliasType:
      return u.resolved.specialization
    default:
      return .empty
    }
  }

  /// Indicates whether `self` is a leaf type.
  ///
  /// A leaf type is a type whose only subtypes are itself and `Never`.
  public var isLeaf: Bool {
    switch base {
    case let t as BoundGenericType:
      return t.base.isLeaf
    case is ExistentialType, is ArrowType, is TypeVariable:
      return false
    case let t as TypeAliasType:
      return t.resolved.isLeaf
    case let t as UnionType:
      return t.elements.isEmpty
    default:
      return true
    }
  }

  /// Indicates whether `self` is the error type.
  public var isError: Bool {
    base is ErrorType
  }

  /// Indicates whether `self` is a built-in type.
  ///
  /// - Requires: `self` is canonical.
  public var isBuiltin: Bool {
    precondition(isCanonical)
    return base is BuiltinType
  }

  /// Indicates whether `self` is a built-in integer type.
  ///
  /// - Requires: `self` is canonical.
  public var isBuiltinInteger: Bool {
    precondition(isCanonical)
    if let b = BuiltinType(self) {
      return b.isInteger
    } else {
      return false
    }
  }

  /// `true` iff `self` is a built-in type or tuple thereof.
  ///
  /// - Requires: `self` is canonical.
  public var isBuiltinOrRawTuple: Bool {
    precondition(isCanonical)
    if let b = TupleType(self) {
      return b.elements.allSatisfy(\.type.isBuiltin)
    } else {
      return base is BuiltinType
    }
  }

  /// `true` iff `self` is syntactically equal to Hylo's `Void` or `Never` type.
  public var isVoidOrNever: Bool {
    isVoid || isNever
  }

  /// `true` iff `self` is syntactically equal to Hylo's `Void` type.
  public var isVoid: Bool {
    self == .void
  }

  /// `true` iff `self` is syntactically equal to Hylo's `Never` type.
  public var isNever: Bool {
    self == .never
  }

  /// `true` iff `self` is a generic type parameter or associated type.
  public var isTypeParameter: Bool {
    (base is AssociatedTypeType) || (base is GenericTypeParameterType)
  }

  /// `true` iff `self` is a type variable.
  public var isVariable: Bool {
    base is TypeVariable
  }

  /// Returns `true` iff `self` is bound to an existential quantifier.
  public var isSkolem: Bool {
    switch base {
    case let u as AssociatedTypeType:
      return u.domain.isSkolem
    case is GenericTypeParameterType:
      return true
    case let u as ConformanceLensType:
      return u.subject.isSkolem
    default:
      return false
    }
  }

  /// Indicates whether `self` has a record layout.
  public var hasRecordLayout: Bool {
    switch base {
    case is BufferType, is ArrowType, is ProductType, is TupleType:
      return true
    case let type as BoundGenericType:
      return type.base.hasRecordLayout
    default:
      return false
    }
  }

  /// Returns `self` with occurrences of free type variables replaced by errors.
  public var replacingVariablesWithErrors: AnyType {
    self.transform { (t) in
      if t.base is TypeVariable {
        return .stepOver(.error)
      } else if t[.hasVariable] {
        return .stepInto(t)
      } else {
        return .stepOver(t)
      }
    }
  }

  /// Inserts the type variables that occur free in `self` into `s`.
  public func collectOpenVariables(in s: inout Set<TypeVariable>) {
    forEachOpenVariable(mutate: &s, with: { (partialResult, v) in partialResult.insert(v) })
  }

  /// Calls `action` on `m` and each type variable that occurs free in `self`.
  public func forEachOpenVariable<T>(
    mutate m: inout T, with action: (inout T, TypeVariable) -> Void
  ) {
    _ = self.transform(mutating: &m) { (s, t) in
      if let v = TypeVariable(t) {
        action(&s, v)
        return .stepOver(t)
      } else if t[.hasVariable] {
        return .stepInto(t)
      } else {
        return .stepOver(t)
      }
    }
  }

  /// Returns the generic parameters occurring free in `self`.
  public var skolems: OrderedSet<GenericParameterDecl.ID> {
    var r = OrderedSet<GenericParameterDecl.ID>()
    collectGenericTypeParameters(in: &r, ignoring: [])
    return r
  }

  /// Inserts generic parameters occurring free in `self` into `open`, unless they're in `bound`.
  private func collectGenericTypeParameters(
    in open: inout OrderedSet<GenericParameterDecl.ID>,
    ignoring bound: Set<GenericParameterDecl.ID>
  ) {
    var state = (bound: bound, open: open)
    defer { open = state.open }

    _ = self.transform(mutating: &state) { (s, t) in
      switch t.base {
      case let u as BoundGenericType:
        var b = s.bound
        for (k, v) in u.arguments {
          b.insert(k)
          if let g = GenericTypeParameterType(v.asType), g.decl == k {
            if !s.bound.contains(k) { s.open.append(k) }
          }
        }
        for a in u.arguments.values {
          a.asType?.collectGenericTypeParameters(in: &s.open, ignoring: b)
        }
        return .stepOver(t)

      case let u as GenericTypeParameterType:
        if !s.bound.contains(u.decl) { s.open.append(u.decl) }
        return .stepOver(t)

      default:
        return t[.hasSkolem] ? .stepInto(t) : .stepOver(t)
      }
    }
  }

}

extension AnyType: TypeProtocol {

  public var flags: ValueFlags { base.flags }

  public func transformParts<M>(
    mutating m: inout M, _ transformer: (inout M, AnyType) -> TypeTransformAction
  ) -> AnyType {
    AnyType(wrapped.transformParts(mutating: &m, transformer))
  }

}

extension AnyType: Equatable {

  /// Returns whether `l` is syntactically equal to `r`.
  public static func == (l: Self, r: Self) -> Bool {
    l.wrapped.equals(r.wrapped)
  }

  /// Returns whether `l` is syntactically equal to `r`.
  public static func == <T: TypeProtocol>(l: Self, r: T) -> Bool {
    l.wrapped.unwrap(as: T.self) == r
  }

  /// Returns whether `l` is not syntactically equal to `r`.
  public static func != <T: TypeProtocol>(l: Self, r: T) -> Bool {
    !(l == r)
  }

  /// Returns whether `l` is syntactically equal to `r`.
  public static func == <T: TypeProtocol>(l: T, r: Self) -> Bool {
    l == r.wrapped.unwrap(as: T.self)
  }

  /// Returns whether `l` is not syntactically equal to `r`.
  public static func != <T: TypeProtocol>(l: T, r: Self) -> Bool {
    !(l == r)
  }

  /// Returns whether `subject` syntactically matches `pattern`.
  ///
  /// This operator is used in switch statements to match the wrapped value of an `AnyType`.
  ///
  ///     func foo(_ x: AnyType) {
  ///       switch x.base {
  ///       case AnyType.any:
  ///         print("type is 'Any'")
  ///       case AnyType.never:
  ///         print("type is 'Never'")
  ///       default:
  ///         print("type is neither 'Any' nor 'Never'")
  ///       }
  ///     }
  public static func ~= (pattern: Self, subject: any TypeProtocol) -> Bool {
    pattern == subject
  }

  /// Returns whether `subject` syntactically matches `pattern`.
  public static func ~= (pattern: Self, subject: Self) -> Bool {
    pattern == subject
  }

  /// Returns whether `subject` syntactically matches `pattern`.
  public static func ~= <T: TypeProtocol>(pattern: T, subject: Self) -> Bool {
    pattern == subject
  }

}

extension AnyType: Hashable {

  public func hash(into hasher: inout Hasher) {
    wrapped.hash(into: &hasher)
  }

}

extension AnyType: CustomStringConvertible {

  public var description: String { String(describing: base) }

}

/// Creates a type-erased container wrapping the given instance.
public prefix func ^ <T: TypeProtocol>(_ base: T) -> AnyType {
  AnyType(base)
}
