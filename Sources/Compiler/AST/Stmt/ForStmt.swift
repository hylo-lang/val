/// A for loop.
public struct ForStmt: Stmt, LexicalScope {

  public static let kind = NodeKind.forStmt

  /// The conditional binding of the loop.
  public var binding: NodeID<BindingDecl>

  /// The iteration domain of the loop.
  public var domain: AnyExprID

  /// The filter of the loop, if any.
  public var filter: AnyExprID?

  /// The body of the loop.
  public var body: NodeID<BraceStmt>

}
