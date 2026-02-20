use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

pub use indexmap::IndexSet;

#[derive(Debug, Clone)]
pub struct DirectedGraph<N: Clone + Debug + Eq + PartialEq + Hash> {
    adjacency_list: HashMap<N, IndexSet<N>>,
}

impl<N: Clone + Debug + Eq + PartialEq + Hash> Default for DirectedGraph<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: Clone + Debug + Eq + PartialEq + Hash> DirectedGraph<N> {
    pub fn new() -> Self {
        DirectedGraph {
            adjacency_list: HashMap::new(),
        }
    }

    pub fn contains(&self, n: N) -> bool {
        self.adjacency_list.contains_key(&n)
    }

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
                let mut end_set = IndexSet::new();
                ends_vec.iter().for_each(|end| {
                    if !end_set.contains(end) {
                        end_set.insert(end.clone());
                    }
                });
                end_set
            });
    }

    pub fn get_edges(&self, n: N) -> Option<&IndexSet<N>> {
        self.adjacency_list.get(&n)
    }

    pub fn node_count(&self) -> usize {
        self.adjacency_list.len()
    }

    pub fn edge_count(&self) -> usize {
        self.adjacency_list.values().map(|edges| edges.len()).sum()
    }

    pub fn remove_node(&mut self, n: N) -> Option<IndexSet<N>> {
        self.adjacency_list.remove(&n)
    }

    pub fn remove_edge(&mut self, start: N, end: N) -> bool {
        match self.adjacency_list.get_mut(&start) {
            Some(ends) => ends.shift_remove(&end),
            None => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::DirectedGraph;

    #[test]
    fn test_string_graph() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node("Alice", vec![]);
        assert!(digraph.contains("Alice"));
        digraph.add_node("Bob", vec!["Eve"]);
        assert!(digraph.contains("Bob"));
        assert!(!digraph.contains("Eve"));
        digraph.add_node("Carl", vec!["Alice", "Bob"]);
        assert!(digraph.contains("Carl"));
    }

    #[test]
    fn test_integer_graph() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![]);
        assert!(digraph.contains(1));
        digraph.add_node(2, vec![3]);
        assert!(digraph.contains(2));
        assert!(!digraph.contains(3));
        digraph.add_node(-3, vec![1, 2]);
        assert!(digraph.contains(-3));
    }

    #[test]
    fn test_get_edges() {
        let mut digraph = DirectedGraph::new();
        digraph.add_node(1, vec![2, 3]);
        let edges_of_1 = digraph.get_edges(1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert!(edges_of_1.contains(&2));
        assert!(edges_of_1.contains(&3));

        digraph.add_node(11, vec![22]);
        digraph.add_node(11, vec![33]);
        let edges_of_11 = digraph.get_edges(11);
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
        assert!(!digraph.remove_edge(2, 3));
        let edges_of_1 = digraph.get_edges(1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert_eq!(edges_of_1.len(), 2);
        assert!(edges_of_1.contains(&2));
        assert!(edges_of_1.contains(&3));
        assert!(digraph.remove_edge(1, 3));
        let edges_of_1 = digraph.get_edges(1);
        assert!(edges_of_1.is_some());
        let edges_of_1 = edges_of_1.unwrap();
        assert_eq!(edges_of_1.len(), 1);
        assert!(edges_of_1.contains(&2));
        assert!(!edges_of_1.contains(&3));
    }
}
