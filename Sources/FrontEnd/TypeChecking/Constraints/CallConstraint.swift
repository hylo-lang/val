import Utils

/// A constraint `F(A1, ..., An) -> R` or `F[A1, ..., An]: R` specifying that `F` is the type of a
/// callable object that returns or projects (respectively) instances of `R` when called with
/// arguments of types `A1, ..., An`.
struct CallConstraint: Constraint, Hashable {

  /// The label, type, and site of an argument passed to a callable object.
  struct Argument: Hashable {

    /// The label of the argument.
    let label: SourceRepresentable<String>?

    /// The type of the argument.
    fileprivate(set) var type: AnyType

    /// The site from which the argument's value was parsed.
    let valueSite: SourceRange

  }

  /// A type assumed to be callable.
  private(set) var callee: AnyType

  /// The arguments passed to `callee`.
  private(set) var arguments: [Argument]

  /// The expected output type of `callee`.
  private(set) var output: AnyType

  /// The call associated with this constraint.
  let call: CallID

  /// `true` if `callee` is expected to be an arrow; `false` if it's expected to be a subscript.
  let isArrow: Bool

  /// `true` if `callee` is marked for mutation.
  let isMutating: Bool

  let origin: ConstraintOrigin

  /// Creates a constraint requiring `callee` to be the type of an arrow that accepts given
  /// `arguments` and returns `output`.
  init(
    arrow callee: AnyType,
    usedMutably isMutating: Bool,
    takes arguments: [Argument],
    gives output: AnyType,
    in call: CallID,
    origin: ConstraintOrigin
  ) {
    self.callee = callee
    self.arguments = arguments
    self.output = output
    self.call = call
    self.isArrow = true
    self.isMutating = isMutating
    self.origin = origin
  }

  /// Creates a constraint requiring `callee` to be the type of a subscript that accepts given
  /// `arguments` and returns `output`.
  init(
    subscript callee: AnyType,
    usedMutably isMutating: Bool,
    takes arguments: [Argument],
    gives output: AnyType,
    in call: CallID,
    origin: ConstraintOrigin
  ) {
    self.callee = callee
    self.arguments = arguments
    self.output = output
    self.call = call
    self.isArrow = false
    self.isMutating = isMutating
    self.origin = origin
  }

  /// The expected labels of `callee`.
  var labels: LazyMapSequence<[Argument], String?> {
    arguments.lazy.map(\.label?.value)
  }

  /// Inserts the type variables that occur free in `self` into `s`.
  func collectOpenVariables(in s: inout Set<TypeVariable>) {
    callee.collectOpenVariables(in: &s)
    output.collectOpenVariables(in: &s)
    for i in 0..<arguments.count {
      arguments[i].type.collectOpenVariables(in: &s)
    }
  }

  mutating func modifyTypes(_ transform: (AnyType) -> AnyType) {
    update(&callee, with: transform)
    update(&output, with: transform)
    for i in 0..<arguments.count {
      update(&arguments[i].type, with: transform)
    }
  }

}

extension CallConstraint: CustomStringConvertible {

  var description: String {
    let m = isMutating ? "&" : ""
    if isArrow {
      return "\(m)(\(callee))(\(list: arguments)) -> \(output)"
    } else {
      return "\(m)(\(callee))[\(list: arguments)]: \(output)"
    }
  }

}

extension CallConstraint.Argument: CustomStringConvertible {

  var description: String {
    if let l = label {
      return "\(l.value): \(type)"
    } else {
      return "\(type)"
    }
  }

}
