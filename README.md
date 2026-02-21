# Directed Graph

[![Rust CI](https://github.com/trislu/directed-graph/actions/workflows/rust.yml/badge.svg)](https://github.com/trislu/directed-graph/actions/workflows/rust.yml)
[![Cargo Publish](https://github.com/trislu/directed-graph/actions/workflows/publish.yml/badge.svg)](https://github.com/trislu/directed-graph/actions/workflows/publish.yml)
[![Latest Version](https://img.shields.io/crates/v/directed-graph.svg)](https://crates.io/crates/directed-graph)
[![License](https://img.shields.io/crates/l/directed-graph.svg)](LICENSE)

A **type-safe, generic directed graph implementation** for Rust

## Installation

Add the following to the `dependencies` section of your `Cargo.toml`:

```toml
[dependencies]
directed_graph = { path = "./path-to-this-crate" } # For local development
# Or use the crates.io published version:
# directed_graph = "0.1.0"
```

## Basic Usage

### Graph Manipulation

```rust
use directed_graph::DirectedGraph;
// Initialize an empty directed graph with integer nodes
let mut graph = DirectedGraph::new();
// Add nodes with outgoing edges (duplicate edges are automatically ignored)
graph.add_node(1, vec![2, 3]); // Node 1 -> 2, 1 -> 3
graph.add_node(2, vec![3]);    // Node 2 -> 3
graph.add_node(1, vec![3, 4]); // Append edge 1 -> 4 (3 is a duplicate and ignored)
graph.add_node(3, vec![]);     // Add an isolated node with no outgoing edges
// Check if a node exists in the graph
assert!(graph.contains(&1));
assert!(!graph.contains(&5));
// Query the adjacent nodes (outgoing edges) of a given node
let adj_1 = graph.get_adjacent_nodes(&1).unwrap();
assert!(adj_1.contains(&2) && adj_1.contains(&4));
```

### Retrieve Graph Statistics

```rust
// Count the unique nodes and edges in the graph
assert_eq!(graph.node_count(), 4); // Nodes in graph: 1, 2, 3, 4
assert_eq!(graph.edge_count(), 4); // Edges in graph: 1->2, 1->3, 1->4, 2->3
```

### Remove Nodes & Edges

```rust
// Remove a single directed edge (1 -> 3)
assert!(graph.remove_edge(1, 3)); // Returns true (edge exists and is removed)
assert!(!graph.remove_edge(1, 5)); // Returns false (edge does not exist)
assert_eq!(graph.edge_count(), 3);
// Remove a node and all its outgoing edges from the graph
let removed_edges = graph.remove_node(2).unwrap();
assert_eq!(removed_edges.len(), 1); // Node 2 had one outgoing edge: 2->3
assert!(!graph.contains(&2)); // Node 2 is no longer in the graph
assert_eq!(graph.node_count(), 3);
```

### Graph Analysis

See `analyze` module for more

```rust
use directed_graph::{DirectedGraph, analyze};
// Create a cyclic directed graph
let mut cyclic_graph = DirectedGraph::new();
cyclic_graph.add_node(1, vec![2]);
cyclic_graph.add_node(2, vec![3]);
cyclic_graph.add_node(3, vec![1]);
// Run graph analysis
let result = analyze::analyze_digraph(&cyclic_graph);
// Detect cycles in the graph
assert!(!result.is_acyclic());
assert!(result.get_elementary_cycles().contains(&vec![1, 2, 3]));

// Create an acyclic directed graph (DAG)
let mut dag = DirectedGraph::new();
dag.add_node(1, vec![2]);
dag.add_node(2, vec![3]);
let result = analyze::analyze_digraph(&dag);
assert!(result.is_acyclic());
```

### Using Custom Node Types (Not Recommended)

We **recommend associating your node instances with a unique identifier** (e.g., `u64` or `String`). If you choose to use a custom node type regardless, refer to the `test_custom_node()` test case in the crate's test suite for implementation guidance.

You will need to manually implement the following Rust traits for your custom type:

- `Eq`
- `PartialEq`
- `Hash`
- `PartialOrd`
- `Ord`

## Algorithm

This implementation leverages classic cycle-detection algorithms for directed graphs, with core logic based on the following foundational works:

- Tarjan, R. (1973). Enumeration of the elementary circuits of a directed graph. *SIAM Journal on Computing*, 2(3), 211–216.
- Szwarcfiter, J. L., & Lauer, P. E. (1976). A search strategy for the elementary cycles of a directed graph. *BIT Numerical Mathematics*, 16(2), 192–204.

## License

This project is licensed under the [**MIT License**](LICENSE)
