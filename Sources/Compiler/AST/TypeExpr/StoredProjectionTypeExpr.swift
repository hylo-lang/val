/// The type expression of a stored projection.
public struct StoredProjectionTypeExpr: TypeExpr {

  public static let kind = NodeKind.storedProjectionTypeExpr

  public enum Introducer: Hashable {

    case `let`

    case `inout`

  }

  public var introducer: SourceRepresentable<Introducer>

  /// The expression of the projected type.
  public var operand: AnyTypeExprID

}
