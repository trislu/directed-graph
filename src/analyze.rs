use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::DirectedGraph;

#[derive(Debug, Clone)]
pub struct AnalyzeResult<N: Clone + Debug + Eq + PartialEq + Hash> {
    undefines: HashSet<N>,
    selfloops: HashSet<N>,
}

impl<N: Clone + Debug + Eq + PartialEq + Hash> AnalyzeResult<N> {
    pub fn new() -> Self {
        AnalyzeResult {
            undefines: HashSet::new(),
            selfloops: HashSet::new(),
        }
    }

    pub fn undefined_nodes(&self) -> &HashSet<N> {
        &self.undefines
    }

    pub fn selfloop_nodes(&self) -> &HashSet<N> {
        &self.selfloops
    }

    pub fn is_complete(&self) -> bool {
        self.undefined_nodes().is_empty()
    }
}

impl<N: Clone + Debug + Eq + PartialEq + Hash> Default for AnalyzeResult<N> {
    fn default() -> Self {
        Self::new()
    }
}

pub fn analyze_digraph<N>(digraph: &DirectedGraph<N>) -> AnalyzeResult<N>
where
    N: Clone + Debug + Eq + PartialEq + Hash,
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
    result
}

#[cfg(test)]
mod tests {
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
}
