use crate::{DirectedGraph, NodeConstraints};
use std::borrow::Cow;
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

/// Generates a 64-bit hash value for a given hashable value (internal helper)
fn get_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

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
    /// assert_eq!(result.get_all_cycles(), &vec![vec![1, 2, 3]]);
    /// ```
    pub fn get_all_cycles(&self) -> &Vec<Vec<N>> {
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

/// Internal enum to track node visit status during DFS cycle detection
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitStatus {
    Unvisited,
    Visiting,
    Visited,
}

/// Standardizes a cycle to avoid duplicate representations (internal helper)
fn standardize_cycle<N>(mut cycle: Vec<N>) -> Option<Vec<N>>
where
    N: NodeConstraints,
{
    // TODO: self-loop is detected before, check if can be optimized.
    if cycle.len() < 2 {
        return None;
    }
    cycle.pop();
    // self-loop
    if cycle.len() == 1 {
        return Some(cycle);
    }
    // TODO: performance improvement?
    cycle.sort();
    Some(cycle)
}

/// Generates a unique 64-bit ID for a standardized cycle (internal helper)
fn cycle_unique_id<N>(cycle: &[N]) -> u64
where
    N: NodeConstraints,
{
    get_hash(&cycle)
}

/// Finds all unique cycles in a directed graph using an iterative DFS approach (internal helper)
///
/// Iterative DFS is used to avoid stack overflow for large graphs. Cycles are standardized and deduplicated
/// to ensure only unique cycles are returned.
fn find_all_cycles<N>(digraph: &DirectedGraph<N>) -> Vec<Vec<N>>
where
    N: NodeConstraints,
{
    let mut all_cycles = Vec::new();
    let mut cycle_dup_set = HashSet::new();
    let mut visit_status = HashMap::new();
    for node in digraph.adjacency_list.keys() {
        visit_status.insert(node.clone(), VisitStatus::Unvisited);
    }
    // Helper stack for DFS traversing, to avoid stack-overflow on recursion
    struct StackFrame<'a, N>
    where
        [N]: ToOwned,
    {
        current: N,             // current node
        adjacent_id: usize,     // which adjacency node of current node (is processing)
        dfs_path: Cow<'a, [N]>, // the DFS traverse path
        processed: bool,        // if current node is processed
    }
    for start_node in digraph.adjacency_list.keys() {
        // TODO: skip the isolated & ingore self-loop cycles?
        if visit_status[start_node] == VisitStatus::Unvisited {
            let mut stack = vec![StackFrame {
                current: start_node.clone(),
                adjacent_id: 0usize,
                dfs_path: Cow::Owned(vec![start_node.clone()]),
                processed: false,
            }];
            // fresh start "visiting"
            visit_status.insert(start_node.clone(), VisitStatus::Visiting);
            while let Some(frame) = stack.pop() {
                if !frame.processed {
                    stack.push(StackFrame {
                        current: frame.current.clone(),
                        adjacent_id: frame.adjacent_id,
                        dfs_path: frame.dfs_path.clone(),
                        processed: true,
                    });
                    let Some(adj_nodes) = digraph.get_adjacent_nodes(&frame.current) else {
                        continue;
                    };
                    let adj_nodes: Vec<&N> = adj_nodes.iter().collect();
                    // Will the first adjacency be skipped?
                    for (i, _) in adj_nodes.iter().enumerate().skip(frame.adjacent_id) {
                        let next_node = adj_nodes[i].clone();
                        match visit_status.get(&next_node) {
                            // Scenario1: status of next node is "visiting"
                            Some(&VisitStatus::Visiting) => {
                                // hitting back in dfs_path, i.e., where the cycle starts
                                if let Some(cycle_start_idx) =
                                    &frame.dfs_path.iter().position(|n| *n == next_node)
                                {
                                    let mut cycle = frame.dfs_path.clone()
                                        [*cycle_start_idx..frame.dfs_path.len()]
                                        .to_vec();
                                    cycle.push(next_node.clone());
                                    // Since nodes are partial-oredered, we can "count" the cycle
                                    if let Some(standard_cycle) = standardize_cycle(cycle) {
                                        let cycle_uid = cycle_unique_id(&standard_cycle);
                                        if !cycle_dup_set.contains(&cycle_uid) {
                                            cycle_dup_set.insert(cycle_uid);
                                            all_cycles.push(standard_cycle);
                                        }
                                    }
                                }
                            }
                            // Scenario2: status of next node is "unvisited"
                            Some(&VisitStatus::Unvisited) => {
                                // mark it as "visiting"
                                visit_status.insert(next_node.clone(), VisitStatus::Visiting);
                                // record current frame
                                stack.push(StackFrame {
                                    current: frame.current.clone(),
                                    adjacent_id: i + 1,
                                    dfs_path: frame.dfs_path.clone(),
                                    processed: false,
                                });
                                // move in next node, start analyzing the adjacencies of which
                                let mut new_dfs_path = frame.dfs_path.into_owned();
                                new_dfs_path.push(next_node.clone());
                                let new_frame = StackFrame {
                                    current: next_node,
                                    adjacent_id: 0,
                                    dfs_path: Cow::Owned(new_dfs_path),
                                    processed: false,
                                };
                                stack.push(new_frame);
                                // Break for DFS, let while loop pop the next node
                                break;
                            }
                            // Scenario3: next node is "visited"
                            Some(&VisitStatus::Visited) | None => continue,
                        }
                    }
                } else {
                    // DFS traversing back, mark this node as "visited"
                    visit_status.insert(frame.current.clone(), VisitStatus::Visited);
                }
            }
        }
    }
    all_cycles
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
/// assert_eq!(result.get_all_cycles(), &vec![vec![1], vec![1, 2, 3]]);
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
    let mut result = AnalyzeResult::default();
    digraph.adjacency_list.iter().for_each(|(start, ends)| {
        ends.iter().for_each(|end| {
            if !digraph.contains(end) {
                result.undefines.insert(end.clone());
            }
            if end == start {
                result.selfloops.insert(end.clone());
            }
        });
    });
    // TODO: improve performance
    result.cycles = find_all_cycles(digraph);
    result
}

#[cfg(test)]
mod tests {
    use crate::{
        DirectedGraph,
        analyze::{analyze_digraph, find_all_cycles},
    };
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
        let cycles = find_all_cycles(&digraph);
        assert!(cycles.is_empty());
    }
    #[test]
    fn test_single_cycle() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2]); // 1->2
        digraph.add_node(2, vec![3]); // 2->3
        digraph.add_node(3, vec![1]); // 3->1 (cycle)
        let cycles = find_all_cycles(&digraph);
        assert!(!cycles.is_empty());
        assert_eq!(cycles.len(), 1);
        assert_eq!(cycles[0], vec![1, 2, 3]);
    }
    #[test]
    fn test_self_loop() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![1]); // 1->1 (self-loop)
        digraph.add_node(2, vec![3]);
        let cycles = find_all_cycles(&digraph);
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
        let cycles = find_all_cycles(&digraph);
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
        let cycles = find_all_cycles(&digraph);
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
        let cycles = find_all_cycles(&digraph);
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
        let cycles = result.get_all_cycles();
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
        let cycles = result.get_all_cycles();
        assert!(cycles.is_empty());
    }
}
