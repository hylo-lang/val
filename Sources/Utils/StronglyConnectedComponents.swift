/// The strongly connected components of a directed graph.
public struct StronglyConnectedComponents<Vertex: Hashable> {

  /// A map from vertex identifier to its properties.
  private var properties: [Vertex: Properties] = [:]

  /// A map from component to its vertices.
  private var components: [[Vertex]] = []

  /// The stack of vertices being visited.
  private var stack: [Vertex] = []

  /// The next vertex index.
  private var nextIndex: Int = 0

  /// Creates an empty instance.
  public init() {}

  /// Returns the vertices in the given component.
  public func vertices(in c: Int) -> [Vertex] {
    components[c]
  }

  /// Returns the strongly connected component containing `v`, calling `enumerateSuccessors` to
  /// obtain the successors of a vertex.
  public mutating func component(
    containing v: Vertex,
    enumeratingSuccessorsWith enumerateSuccessors: (Vertex) -> [Vertex]
  ) -> Int {
    if let c = properties[v]?.component { return c }

    properties[v] = .init(low: nextIndex, index: nextIndex, component: -1, isOnStack: true)
    stack.append(v)
    nextIndex += 1

    for w in enumerateSuccessors(v) {
      if properties[w] == nil {
        // Successor w has not yet been visited; recurse on it
        _ = component(containing: w, enumeratingSuccessorsWith: enumerateSuccessors)
        properties[v]!.low = min(properties[v]!.low, properties[w]!.low)
      } else if properties[w]!.isOnStack {
        properties[v]!.low = min(properties[v]!.low, properties[w]!.index)
      }
    }

    if properties[v]!.low == properties[v]!.index {
      let c = components.count
      components.append([])

      while true {
        let w = stack.removeLast()
        components[c].append(w)
        modify(&properties[w]!) { (pw) in
          pw.isOnStack = false
          pw.component = c
        }
        if w == v { break }
      }
    }

    return properties[v]!.component
  }

  /// The properties associated with a vertex in Tarjan's algorithm.
  private struct Properties {

    /// The smallest index of any vertex reachable from this vertex.
    var low: Int

    /// The index of this vertex.
    var index: Int

    /// The component in which this vertex belongs.
    var component: Int

    /// True iff this vertex is on the stack.
    var isOnStack: Bool

  }

}
