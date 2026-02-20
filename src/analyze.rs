use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use crate::{DirectedGraph, NodeConstraints};

fn get_hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = DefaultHasher::new();
    value.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, Clone)]
pub struct AnalyzeResult<N: NodeConstraints> {
    undefines: HashSet<N>,
    selfloops: HashSet<N>,
    cycles: Vec<Vec<N>>,
}

impl<N: NodeConstraints> AnalyzeResult<N> {
    pub fn new() -> Self {
        AnalyzeResult {
            undefines: HashSet::new(),
            selfloops: HashSet::new(),
            cycles: vec![],
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

    pub fn is_acyclic(&self) -> bool {
        self.cycles.is_empty()
    }

    pub fn get_all_cycles(&self) -> &Vec<Vec<N>> {
        &self.cycles
    }
}

impl<N: NodeConstraints> Default for AnalyzeResult<N> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VisitStatus {
    Unvisited,
    Visiting,
    Visited,
}

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

fn cycle_unique_id<N>(cycle: &[N]) -> u64
where
    N: NodeConstraints,
{
    get_hash(&cycle)
}

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
    struct StackFrame<N> {
        current: N,         // current node
        adjacent_id: usize, // which adjacency node of current node (is processing)
        dfs_path: Vec<N>,   // the DFS traverse path
        processed: bool,    // if current node is processed
    }

    for start_node in digraph.adjacency_list.keys() {
        // TODO: skip the isolated & ingore self-loop cycles?
        if visit_status[start_node] == VisitStatus::Unvisited {
            let mut stack = vec![StackFrame {
                current: start_node.clone(),
                adjacent_id: 0usize,
                dfs_path: vec![start_node.clone()],
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
                                let mut new_frame = StackFrame {
                                    current: next_node.clone(),
                                    adjacent_id: 0,
                                    dfs_path: vec![],
                                    processed: false,
                                };
                                new_frame.dfs_path.extend(frame.dfs_path);
                                new_frame.dfs_path.push(next_node);
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
