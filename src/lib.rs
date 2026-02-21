//! A generic directed graph implementation with core graph operations and cycle detection capabilities.
//!
//! This crate provides a type-safe `DirectedGraph` structure that supports generic node types
//! (with basic constraints for hashing and ordering) and common graph operations like node/edge
//! addition, removal, adjacency query, and node/edge count statistics. It also includes an
//! `analyze` module for cycle detection in directed graphs.
//!
//! # Key Features
//! - Generic node support (works with all types that implement `NodeConstraints`)
//! - Efficient adjacency list storage with `IndexMap` and `IndexSet`
//! - Core graph operations: add/remove nodes/edges, query adjacent nodes
//! - Node/edge count statistics
//! - Cycle detection and graph analysis (in the `analyze` module)
//!
//! # Basic Usage
//! ```
//! use directed_graph::DirectedGraph;
//!
//! // Create a new directed graph with integer nodes
//! let mut graph = DirectedGraph::new();
//!
//! // Add nodes and edges
//! graph.add_node(1, vec![2, 3]);
//! graph.add_node(2, vec![3]);
//! graph.add_node(3, vec![]);
//!
//! // Query adjacent nodes
//! assert!(graph.get_adjacent_nodes(&1).unwrap().contains(&2));
//!
//! // Get node/edge counts
//! assert_eq!(graph.node_count(), 3);
//! assert_eq!(graph.edge_count(), 3);
//!
//! // Remove an edge
//! graph.remove_edge(&1, &3);
//! assert_eq!(graph.edge_count(), 2);
//! ```

pub use indexmap::IndexMap as NodeMap;
pub use indexmap::IndexSet as NodeSet;
use std::fmt::Debug;
use std::hash::Hash;

mod algorithm;
/// Graph analysis module (cycle detection core logic)
pub mod analyze;

/// Trait defining the core constraints for node types in a `DirectedGraph`.
///
/// Nodes must implement this trait to be used in the directed graph. The trait aggregates
/// common Rust traits required for hashing, equality, ordering, cloning, and debugging—
/// all essential for graph storage and operations (e.g., `IndexMap` keys, set operations).
///
/// This trait is **automatically implemented** for all types that satisfy the underlying bounds,
/// so you do not need to implement it manually for your custom node types.
pub trait NodeConstraints: Clone + Debug + Eq + PartialEq + Hash + PartialOrd + Ord {}

// Automatic implementation for all types meeting the NodeConstraints bounds
impl<T> NodeConstraints for T where T: Clone + Debug + Eq + PartialEq + Hash + PartialOrd + Ord {}

/// A generic directed graph data structure implemented with an adjacency list.
///
/// The graph uses a `IndexMap` to map each node to an `IndexSet` of its adjacent nodes (outgoing edges),
/// ensuring efficient:
/// - Node/edge lookups (O(1) average for hash map)
/// - Duplicate edge prevention (via `IndexSet`)
/// - Node/edge addition/removal
///
/// The node type `N` must implement the `NodeConstraints` trait for core operations.
#[derive(Debug, Clone)]
pub struct DirectedGraph<N: NodeConstraints> {
    /// Internal adjacency list storage: maps each node to its set of adjacent nodes (outgoing edges)
    adjacency_list: NodeMap<N, NodeSet<N>>,
}

impl<N: NodeConstraints> Default for DirectedGraph<N> {
    /// Create a new empty `DirectedGraph` using the default implementation.
    ///
    /// Equivalent to calling `DirectedGraph::new()`.
    fn default() -> Self {
        Self::new()
    }
}

impl<N: NodeConstraints> DirectedGraph<N> {
    /// Create a new empty directed graph.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let graph: DirectedGraph<u32> = DirectedGraph::new();
    /// assert_eq!(graph.node_count(), 0);
    /// ```
    pub fn new() -> Self {
        DirectedGraph {
            adjacency_list: NodeMap::new(),
        }
    }

    /// Check if the graph contains a specific node.
    ///
    /// # Arguments
    /// * `n` - Reference to the node to check for existence
    ///
    /// # Returns
    /// `true` if the node exists in the graph, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node("Alice", vec![]);
    /// assert!(graph.contains(&"Alice"));
    /// assert!(!graph.contains(&"Bob"));
    /// ```
    pub fn contains(&self, n: &N) -> bool {
        self.adjacency_list.contains_key(n)
    }

    /// Add a node to the graph with a list of outgoing edges (adjacent nodes).
    ///
    /// If the node **already exists** in the graph, the new edges are **appended** (duplicate edges are ignored).
    /// If the node **does not exist**, it is created with the provided outgoing edges.
    ///
    /// # Arguments
    /// * `start` - The node to add to the graph (source node for the outgoing edges)
    /// * `ends_vec` - Vector of adjacent nodes (target nodes for the outgoing edges from `start`)
    ///
    /// # Notes
    /// - The target nodes in `ends_vec` **do not need to exist** in the graph (orphaned edges are allowed)
    /// - Duplicate edges in `ends_vec` are automatically removed (via `IndexSet`)
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// // Add a new node with two outgoing edges
    /// graph.add_node(1, vec![2, 3]);
    /// // Append a new edge to an existing node (duplicate 3 is ignored)
    /// graph.add_node(1, vec![3, 4]);
    /// assert!(graph.get_adjacent_nodes(&1).unwrap().contains(&4));
    /// ```
    pub fn add_node(&mut self, start: N, ends_vec: Vec<N>) {
        self.adjacency_list
            .entry(start)
            .and_modify(|end_set| {
                ends_vec.iter().for_each(|end| {
                    if !end_set.contains(end) {
                        end_set.insert(end.clone());
                    }
                });
            })
            .or_insert({
                let mut end_set = NodeSet::new();
                ends_vec.iter().for_each(|end| {
                    if !end_set.contains(end) {
                        end_set.insert(end.clone());
                    }
                });
                end_set
            });
    }

    /// Get the set of adjacent nodes (outgoing edges) for a specific node.
    ///
    /// # Arguments
    /// * `n` - Reference to the node to query for adjacent nodes
    ///
    /// # Returns
    /// `Some(&NodeSet<N>)` if the node exists (containing all adjacent nodes), `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2, 3]);
    /// let adj = graph.get_adjacent_nodes(&1).unwrap();
    /// assert!(adj.contains(&2) && adj.contains(&3));
    /// ```
    pub fn get_adjacent_nodes(&self, n: &N) -> Option<&NodeSet<N>> {
        self.adjacency_list.get(n)
    }

    /// Get the total number of **unique nodes** in the graph.
    ///
    /// # Returns
    /// The count of nodes in the graph (length of the adjacency list).
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2]);
    /// graph.add_node(2, vec![3]);
    /// assert_eq!(graph.node_count(), 2);
    /// ```
    pub fn node_count(&self) -> usize {
        self.adjacency_list.len()
    }

    /// Get the total number of **unique edges** in the graph.
    ///
    /// Counts all outgoing edges across all nodes (duplicate edges are not counted, via `IndexSet`).
    ///
    /// # Returns
    /// The total number of unique outgoing edges in the graph.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2, 3]);
    /// graph.add_node(2, vec![3]);
    /// assert_eq!(graph.edge_count(), 3);
    /// ```
    pub fn edge_count(&self) -> usize {
        self.adjacency_list.values().map(|edges| edges.len()).sum()
    }

    /// Remove a node from the graph and return its outgoing edges (if the node existed).
    ///
    /// Removes the node **and all its outgoing edges** from the adjacency list. Incoming edges to this node
    /// are **not removed** (they remain as orphaned edges from other nodes).
    ///
    /// # Arguments
    /// * `n` - The node to remove from the graph
    ///
    /// # Returns
    /// `Some(NodeSet<N>)` if the node existed (containing its outgoing edges), `None` otherwise.
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2, 3]);
    /// let edges = graph.remove_node(1).unwrap();
    /// assert_eq!(edges.len(), 2);
    /// assert!(!graph.contains(&1));
    /// ```
    pub fn remove_node(&mut self, n: N) -> Option<NodeSet<N>> {
        self.adjacency_list.shift_remove(&n)
    }

    /// Remove a single outgoing edge from a source node to a target node.
    ///
    /// # Arguments
    /// * `start` - The source node of the edge to remove
    /// * `end` - The target node of the edge to remove
    ///
    /// # Returns
    /// `true` if the edge existed and was removed, `false` otherwise (either the source node
    /// does not exist, or the edge does not exist).
    ///
    /// # Examples
    /// ```
    /// use directed_graph::DirectedGraph;
    /// let mut graph = DirectedGraph::new();
    /// graph.add_node(1, vec![2, 3]);
    /// assert!(graph.remove_edge(&1, &3));
    /// assert!(!graph.remove_edge(&1, &4));
    /// ```
    pub fn remove_edge(&mut self, start: &N, end: &N) -> bool {
        match self.adjacency_list.get_mut(start) {
            Some(ends) => ends.shift_remove(end),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::hash::{Hash, Hasher};

    use crate::DirectedGraph;

    #[test]
    fn test_string_graph() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("Alice", vec![]);
        assert!(digraph.contains(&"Alice"));
        digraph.add_node("Bob", vec!["Eve"]);
        assert!(digraph.contains(&"Bob"));
        assert!(!digraph.contains(&"Eve"));
        digraph.add_node("Carl", vec!["Alice", "Bob"]);
        assert!(digraph.contains(&"Carl"));
    }

    #[test]
    fn test_integer_graph() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![]);
        assert!(digraph.contains(&1));
        digraph.add_node(2, vec![3]);
        assert!(digraph.contains(&2));
        assert!(!digraph.contains(&3));
        digraph.add_node(-3, vec![1, 2]);
        assert!(digraph.contains(&-3));
    }

    #[test]
    fn test_get_edges() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        let edges_of_1 = digraph.get_adjacent_nodes(&1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert!(edges_of_1.contains(&2));
        assert!(edges_of_1.contains(&3));
        digraph.add_node(11, vec![22]);
        digraph.add_node(11, vec![33]);
        let edges_of_11 = digraph.get_adjacent_nodes(&11);
        assert!(edges_of_11.is_some());
        let edges_of_11 = edges_of_11.unwrap();
        assert!(edges_of_11.contains(&22));
        assert!(edges_of_11.contains(&33));
    }

    #[test]
    fn test_node_count() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        assert_eq!(digraph.node_count(), 1);
        digraph.add_node(11, vec![22]);
        digraph.add_node(11, vec![33]);
        assert_eq!(digraph.node_count(), 2);
    }

    #[test]
    fn test_edge_count() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        assert_eq!(digraph.edge_count(), 2);
        digraph.add_node(11, vec![22]);
        digraph.add_node(11, vec![33]);
        assert_eq!(digraph.edge_count(), 4);
    }

    #[test]
    fn test_remove_node() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        assert_eq!(digraph.remove_node(2), None);
        let edges_of_1 = digraph.remove_node(1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert_eq!(edges_of_1.len(), 2);
        assert!(edges_of_1.contains(&2));
        assert!(edges_of_1.contains(&3));
    }

    #[test]
    fn test_remove_edge() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        assert!(!digraph.remove_edge(&2, &3));
        let edges_of_1 = digraph.get_adjacent_nodes(&1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert_eq!(edges_of_1.len(), 2);
        assert!(edges_of_1.contains(&2));
        assert!(edges_of_1.contains(&3));
        assert!(digraph.remove_edge(&1, &3));
        let edges_of_1 = digraph.get_adjacent_nodes(&1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert_eq!(edges_of_1.len(), 1);
        assert!(edges_of_1.contains(&2));
        assert!(!edges_of_1.contains(&3));
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
        let mut digraph: DirectedGraph<BigNode> = DirectedGraph::new();
        {
            let node1 = BigNode::new(1);
            let node2 = BigNode::new(2);
            let node3 = BigNode::new(3);
            digraph.add_node(node1.clone(), vec![node2, node3]);
            let edges_of_1 = digraph.get_adjacent_nodes(&node1);
            assert!(edges_of_1.is_some());
            let edges_of_1 = edges_of_1.unwrap();
            assert!(edges_of_1.contains(&BigNode::new(2)));
            assert!(edges_of_1.contains(&BigNode::new(3)));
        }
        {
            let node11 = BigNode::new(11);
            let node22 = BigNode::new(22);
            let node33 = BigNode::new(33);
            digraph.add_node(node11.clone(), vec![node22, node33]);
            let edges_of_11 = digraph.get_adjacent_nodes(&node11);
            assert!(edges_of_11.is_some());
            let edges_of_11 = edges_of_11.unwrap();
            assert!(edges_of_11.contains(&BigNode::new(22)));
            assert!(edges_of_11.contains(&BigNode::new(33)));
        }
    }
}
