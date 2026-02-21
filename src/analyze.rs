use crate::algorithm;
use crate::{DirectedGraph, NodeConstraints, NodeSet, algorithm::CompleteDirectedGraph};
use std::collections::HashSet;
use std::fmt::Debug;

/// The result of a directed graph analysis, containing undefined nodes, self-loop nodes and detected cycles.
///
/// This struct aggregates all key insights from a graph analysis:
/// - Nodes that are referenced as targets but do not exist in the graph (undefined nodes)
/// - Nodes that have an edge pointing to themselves (self-loop nodes)
/// - All unique cycles detected in the graph (standardized to avoid duplicates)
///
/// It also provides helper methods to check graph properties (acyclic, complete).
#[derive(Debug, Clone)]
pub struct AnalyzeResult<N: NodeConstraints> {
    undefines: HashSet<N>,
    selfloops: HashSet<N>,
    cycles: Vec<Vec<N>>,
}

impl<N: NodeConstraints> AnalyzeResult<N> {
    /// Create a new empty `AnalyzeResult` with no undefined nodes, self-loops or cycles.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::analyze::AnalyzeResult;
    /// let result: AnalyzeResult<u32> = AnalyzeResult::new();
    /// assert!(result.undefined_nodes().is_empty());
    /// assert!(result.selfloop_nodes().is_empty());
    /// assert!(result.is_acyclic());
    /// ```
    pub fn new() -> Self {
        AnalyzeResult {
            undefines: HashSet::new(),
            selfloops: HashSet::new(),
            cycles: vec![],
        }
    }

    /// Get an immutable reference to the set of **undefined nodes** in the graph.
    ///
    /// Undefined nodes are target nodes that are referenced by an edge but do not exist as a source node
    /// in the graph (orphaned edge targets).
    ///
    /// # Returns
    /// A reference to a `HashSet<N>` containing all undefined nodes.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2]); // 2 is an undefined node
    /// let result = analyze_digraph(&graph);
    /// assert!(result.undefined_nodes().contains(&2));
    /// ```
    pub fn undefined_nodes(&self) -> &HashSet<N> {
        &self.undefines
    }

    /// Get an immutable reference to the set of **self-loop nodes** in the graph.
    ///
    /// Self-loop nodes are nodes that have an outgoing edge pointing to themselves (e.g., `A -> A`).
    ///
    /// # Returns
    /// A reference to a `HashSet<N>` containing all self-loop nodes.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![1]); // 1 is a self-loop node
    /// let result = analyze_digraph(&graph);
    /// assert!(result.selfloop_nodes().contains(&1));
    /// ```
    pub fn selfloop_nodes(&self) -> &HashSet<N> {
        &self.selfloops
    }

    /// Check if the graph is **complete** (no undefined nodes).
    ///
    /// A complete graph in this context means every target node referenced by an edge exists as a source node
    /// in the graph (no orphaned edge targets).
    ///
    /// # Returns
    /// `true` if there are no undefined nodes, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2]);
    /// let result = analyze_digraph(&graph);
    /// assert!(!result.is_complete());
    ///
    /// graph.add_node(2, vec![]);
    /// let result = analyze_digraph(&graph);
    /// assert!(result.is_complete());
    /// ```
    pub fn is_complete(&self) -> bool {
        self.undefined_nodes().is_empty()
    }

    /// Check if the graph is **acyclic** (no cycles detected).
    ///
    /// An acyclic directed graph (DAG) has no paths that start and end at the same node.
    /// Self-loops are considered cycles and will make this return `false`.
    ///
    /// # Returns
    /// `true` if no cycles are detected, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2]);
    /// graph.add_node(2, vec![3]);
    /// let result = analyze_digraph(&graph);
    /// assert!(result.is_acyclic());
    ///
    /// graph.add_node(3, vec![1]); // Creates a cycle 1->2->3->1
    /// let result = analyze_digraph(&graph);
    /// assert!(!result.is_acyclic());
    /// ```
    pub fn is_acyclic(&self) -> bool {
        self.cycles.is_empty()
    }

    /// Get an immutable reference to all **unique cycles** detected in the graph.
    ///
    /// Cycles are standardized to avoid duplicate representations (e.g., `1->2->3` and `2->3->1` are the same cycle)
    /// and sorted for consistency. Self-loops are represented as a single-element vector (e.g., `vec![1]`).
    ///
    /// # Returns
    /// A reference to a `Vec<Vec<N>>` where each inner vector is a unique standardized cycle.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2]);
    /// graph.add_node(2, vec![3]);
    /// graph.add_node(3, vec![1]);
    /// let result = analyze_digraph(&graph);
    /// assert_eq!(result.get_elementary_cycles(), &vec![vec![1, 2, 3]]);
    /// ```
    pub fn get_elementary_cycles(&self) -> &Vec<Vec<N>> {
        &self.cycles
    }
}

impl<N: NodeConstraints> Default for AnalyzeResult<N> {
    /// Create a default empty `AnalyzeResult` (equivalent to `AnalyzeResult::new()`).
    ///
    /// # Examples
    /// ```
    /// use directed_graph::analyze::AnalyzeResult;
    /// let result: AnalyzeResult<&str> = AnalyzeResult::default();
    /// assert!(result.is_acyclic() && result.is_complete());
    /// ```
    fn default() -> Self {
        Self::new()
    }
}

/// Analyzes a directed graph to detect undefined nodes, self-loop nodes and all unique cycles.
///
/// This is the **main public entry point** for graph analysis. It performs three key checks:
/// 1. Identifies undefined nodes (orphaned edge targets)
/// 2. Identifies self-loop nodes (nodes pointing to themselves)
/// 3. Finds all unique cycles using an iterative DFS algorithm (avoids stack overflow)
///
/// The result is returned as an `AnalyzeResult<N>` struct with helper methods to inspect the graph properties.
///
/// # Arguments
/// * `digraph` - A reference to the `DirectedGraph<N>` to analyze
///
/// # Returns
/// An `AnalyzeResult<N>` containing the analysis results (undefined nodes, self-loops, cycles)
///
/// # Type Constraints
/// The node type `N` must implement the `NodeConstraints` trait (Clone, Debug, Eq, Hash, etc.)
///
/// # Examples
/// ## Basic Graph Analysis
/// ```
/// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
///
/// // Create a graph with a cycle, self-loop and undefined node
/// let mut graph = DirectedGraph::new();
/// graph.add_node(1, vec![1, 2]);  // 1 is a self-loop node
/// graph.add_node(2, vec![3, 4]);  // 4 is an undefined node
/// graph.add_node(3, vec![1]);     // Creates a cycle 1->2->3->1
///
/// // Analyze the graph
/// let result = analyze_digraph(&graph);
///
/// // Inspect results
/// assert!(result.selfloop_nodes().contains(&1));
/// assert!(result.undefined_nodes().contains(&4));
/// assert!(!result.is_acyclic());
/// assert!(!result.is_complete());
/// assert!(result.get_elementary_cycles().contains(&vec![1]));
/// assert!(result.get_elementary_cycles().contains(&vec![1, 2, 3]));
/// ```
///
/// ## Acyclic Complete Graph
/// ```
/// use directed_graph::{DirectedGraph, analyze::analyze_digraph};
/// let mut graph = DirectedGraph::new();
/// graph.add_node("A", vec!["B"]);
/// graph.add_node("B", vec!["C"]);
/// graph.add_node("C", vec![]);
///
/// let result = analyze_digraph(&graph);
/// assert!(result.is_acyclic() && result.is_complete());
/// assert!(result.selfloop_nodes().is_empty());
/// ```
pub fn analyze_digraph<N>(digraph: &DirectedGraph<N>) -> AnalyzeResult<N>
where
    N: NodeConstraints,
{
    // the analyze result
    let mut result = AnalyzeResult::default();
    // Record of the orphaned edges
    let mut orphaned_edges: Vec<(&N, &N)> = vec![];
    // Borrow the whole diagraph. O(N)
    let mut complete_graph: CompleteDirectedGraph<&N> = CompleteDirectedGraph::new();
    digraph.adjacency_list.iter().for_each(|(start, ends)| {
        // Sorted insert with empty IndexSet
        complete_graph.adj.insert_sorted(start, NodeSet::new());
        // Vertex to index conversion
        complete_graph.vertices.insert_sorted(start);
        // Check the end nodes
        ends.iter().for_each(|end| {
            if !digraph.contains(end) {
                // End node is not in the graph
                result.undefines.insert(end.clone());
                orphaned_edges.push((start, end));
            } else if end == start {
                // TODO: maybe we can leave self-loops to the algorithm?
                result.selfloops.insert(end.clone());
            } else {
                // Well-defined edge, add to the borrow_digraph
                complete_graph.adj.entry(start).and_modify(|ends| {
                    ends.insert(end);
                });
            }
        });
    });
    // TODO: improve performance
    let cycles = algorithm::find_cycles_with_scc(&complete_graph);
    result.cycles = cycles
        .into_iter()
        .map(|c| c.into_iter().cloned().collect())
        .collect();
    // TODO: should consider the self-loop node as a cycle or not?
    let self_loop_cycle: Vec<Vec<N>> = result
        .selfloop_nodes()
        .iter()
        .map(|n| vec![n.to_owned()])
        .collect();
    result.cycles.extend(self_loop_cycle);
    result
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use crate::{DirectedGraph, analyze::analyze_digraph};
    #[test]
    fn test_analyze_undefined() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("Alice", vec![]);
        digraph.add_node("Bob", vec!["Eve"]);
        digraph.add_node("Carl", vec!["Alice", "Bob"]);
        let result = analyze_digraph(&digraph);
        assert_eq!(result.undefined_nodes().len(), 1);
        assert!(result.undefined_nodes().contains(&"Eve"));
    }
    #[test]
    fn test_analyze_selfref() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("Alice", vec![]);
        digraph.add_node("Bob", vec!["Bob"]);
        digraph.add_node("Carl", vec!["Alice", "Bob"]);
        let result = analyze_digraph(&digraph);
        assert_eq!(result.selfloop_nodes().len(), 1);
        assert!(result.selfloop_nodes().contains(&"Bob"));
    }
    #[test]
    fn test_analyze_is_complete() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("Alice", vec![]);
        digraph.add_node("Bob", vec!["Eve"]);
        digraph.add_node("Carl", vec!["Alice", "Bob"]);
        let result = analyze_digraph(&digraph);
        assert!(!result.is_complete());
        digraph.add_node("Eve", vec![]);
        let result = analyze_digraph(&digraph);
        assert!(result.is_complete());
    }
    #[test]
    fn test_no_cycle() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        digraph.add_node(2, vec![3]);
        digraph.add_node(3, vec![]);
        let result = analyze_digraph(&digraph);
        assert!(result.cycles.is_empty());
    }
    #[test]
    fn test_single_cycle() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2]); // 1->2
        digraph.add_node(2, vec![3]); // 2->3
        digraph.add_node(3, vec![1]); // 3->1 (cycle)
        let result = analyze_digraph(&digraph);
        let cycles = result.cycles;
        assert!(!cycles.is_empty());
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0], vec![1, 2, 3]);
    }
    #[test]
    fn test_self_loop() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![1]); // 1->1 (self-loop)
        digraph.add_node(2, vec![3]);
        let result = analyze_digraph(&digraph);
        let cycles = result.cycles;
        assert!(!cycles.is_empty());
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0], vec![1]);
    }
    #[test]
    fn test_multiple_cycles() {
        let mut digraph = DirectedGraph::new();
        // 1->2->1
        digraph.add_node(1, vec![2]);
        digraph.add_node(2, vec![1]);
        // 3->4->5->3
        digraph.add_node(3, vec![4]);
        digraph.add_node(4, vec![5]);
        digraph.add_node(5, vec![3]);
        // isolated node
        digraph.add_node(6, vec![]);
        let result = analyze_digraph(&digraph);
        let cycles = result.cycles;
        assert!(!cycles.is_empty());
        assert_eq!(cycles.len(), 2);
        assert!(cycles.contains(&vec![1, 2]) && cycles.contains(&vec![3, 4, 5]));
    }
    #[test]
    fn test_cycle_duplicate_avoid() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2]); // will find 1->2->3->1
        digraph.add_node(2, vec![3]); // will find 2->3->1->2
        digraph.add_node(3, vec![1]); // will find 3->1->2->3
        // 3 cycles are actually identical
        let result = analyze_digraph(&digraph);
        let cycles = result.cycles;
        assert!(!cycles.is_empty());
        assert_eq!(cycles.len(), 1);
        assert!(cycles.contains(&vec![1, 2, 3]));
    }
    #[test]
    fn test_string_node_cycle() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("A", vec!["B"]);
        digraph.add_node("B", vec!["C"]);
        digraph.add_node("C", vec!["A"]);
        let result = analyze_digraph(&digraph);
        let cycles = result.cycles;
        assert!(!cycles.is_empty());
        assert_eq!(cycles[0], vec!["A", "B", "C"]);
    }
    #[test]
    fn test_analyze_some_cycles() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("A", vec!["B"]);
        digraph.add_node("B", vec!["C"]);
        digraph.add_node("C", vec!["A"]);
        let result = analyze_digraph(&digraph);
        assert!(!result.is_acyclic());
        let cycles = result.get_elementary_cycles();
        assert_eq!(cycles[0], vec!["A", "B", "C"]);
    }
    #[test]
    fn test_analyze_no_cycles() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        digraph.add_node(2, vec![3]);
        digraph.add_node(3, vec![]);
        let result = analyze_digraph(&digraph);
        assert!(result.is_acyclic());
        let cycles = result.get_elementary_cycles();
        assert!(cycles.is_empty());
    }

    #[test]
    fn test_custom_node() {
        #[derive(Debug, Clone, Default)]
        struct BigNode {
            id: u64,
            _desc: String,
            _text: Vec<Vec<u32>>,
        }
        impl BigNode {
            pub fn new(id: u64) -> Self {
                BigNode {
                    id,
                    _desc: "some custom big node".to_owned(),
                    _text: vec![vec![8], vec![8], vec![4], vec![8]],
                }
            }
        }
        impl PartialEq for BigNode {
            fn eq(&self, other: &Self) -> bool {
                self.id == other.id
            }
        }
        impl Eq for BigNode {}
        impl Hash for BigNode {
            fn hash<H: Hasher>(&self, state: &mut H) {
                self.id.hash(state);
            }
        }
        // Manual Ord: only compare id (ignore all other fields)
        impl Ord for BigNode {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.id.cmp(&other.id)
            }
        }
        // Manual PartialOrd (required for Ord)
        impl PartialOrd for BigNode {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                // align with Ord
                Some(self.cmp(other))
            }
        }
        // Test 1: Acyclic graph (assert is_acyclic = true)
        let mut acyclic_graph: DirectedGraph<BigNode> = DirectedGraph::new();
        let node1 = BigNode::new(1);
        let node2 = BigNode::new(2);
        let node3 = BigNode::new(3);
        acyclic_graph.add_node(node1.clone(), vec![node2.clone(), node3.clone()]);
        let acyclic_result = analyze_digraph(&acyclic_graph);
        assert!(acyclic_result.is_acyclic());
        assert!(acyclic_result.get_elementary_cycles().is_empty());

        // Test 2: Cyclic graph (assert is_acyclic = false)
        let mut cyclic_graph: DirectedGraph<BigNode> = DirectedGraph::new();
        let node11 = BigNode::new(11);
        let node22 = BigNode::new(22);
        let node33 = BigNode::new(33);
        cyclic_graph.add_node(node11.clone(), vec![node22.clone(), node33.clone()]);
        cyclic_graph.add_node(node22.clone(), vec![node33.clone()]);
        cyclic_graph.add_node(node33.clone(), vec![node11.clone()]);
        let cyclic_result = analyze_digraph(&cyclic_graph);
        assert!(!cyclic_result.is_acyclic());
        assert_eq!(cyclic_result.get_elementary_cycles().len(), 2);
        assert_eq!(
            cyclic_result.get_elementary_cycles()[0],
            vec![BigNode::new(11), BigNode::new(22), BigNode::new(33)]
        );
    }
}
