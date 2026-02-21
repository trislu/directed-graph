use crate::{NodeConstraints, NodeMap, NodeSet};
use std::collections::{HashMap, HashSet};

/// The Complete (No orphaned edges, No self-loop nodes) DirectedGraph
#[derive(Debug, Clone)]
pub(crate) struct CompleteDirectedGraph<N>
where
    N: NodeConstraints,
{
    pub adj: NodeMap<N, NodeSet<N>>,
    pub vertices: NodeSet<N>,
}

impl<N> CompleteDirectedGraph<N>
where
    N: NodeConstraints,
{
    pub fn new() -> Self {
        Self {
            adj: NodeMap::new(),
            vertices: NodeSet::new(),
        }
    }

    /// Add a directed edge u -> v
    #[cfg(test)]
    fn add_edge(&mut self, u: N, v: N) {
        self.vertices.insert(u.clone());
        self.vertices.insert(v.clone());
        self.adj.entry(u).or_default().insert(v);
    }

    /// Extract a subgraph containing only the specified vertices
    fn extract_subgraph(&self, vertices: &HashSet<N>) -> Self {
        let mut subgraph = Self::new();
        for u in vertices {
            if let Some(neighbors) = self.adj.get(u) {
                subgraph.adj.insert(u.clone(), NodeSet::new());
                subgraph.vertices.insert(u.clone());
                for v in neighbors {
                    if vertices.contains(v) {
                        subgraph.adj.entry(u.clone()).and_modify(|e| {
                            e.insert(v.clone());
                        });
                    }
                }
            }
        }
        // See the cargo doc of IndexSet::insert_sorted()
        subgraph.vertices.sort_by(|lhs, rhs| lhs.cmp(rhs));
        subgraph
    }

    /// Get all vertices (sorted)
    fn sorted_vertices(&self) -> Vec<N> {
        let vertices: Vec<N> = self.vertices.iter().cloned().collect();
        //vertices.sort();
        //assert!(vertices.is_sorted());
        vertices
    }
}

/// Tarjan's algorithm stack state enumeration (core of non-recursive implementation)
#[derive(Clone)]
enum TarjanState<N>
where
    N: NodeConstraints,
{
    // First visit to a vertex: initialize index and low_link
    Visit(N),
    // Process adjacent vertices of a vertex: record the current adjacent vertex index being processed
    ProcessNeighbors(N, usize),
    // Backtrack to update low_link: update the low_link of parent vertex u after processing child vertex v
    UpdateLowLink(N, N),
}

/// Tarjan's algorithm to find all Strongly Connected Components (SCC) - fully non-recursive version
fn tarjan_scc<N>(graph: &CompleteDirectedGraph<N>) -> Vec<HashSet<N>>
where
    N: NodeConstraints,
{
    let mut index = 0;
    let mut indices = HashMap::new(); // Vertex -> visit index
    let mut low_links = HashMap::new(); // Vertex -> lowest reachable index
    let mut on_stack = HashSet::new(); // Mark if a vertex is on the stack
    let mut stack = Vec::new(); // Vertex stack for Tarjan's algorithm
    let mut sccs = Vec::new(); // Store all SCCs
    let mut tarjan_stack = Vec::new(); // State stack to simulate recursion

    // Traverse all unvisited vertices
    for vertex in graph.sorted_vertices() {
        if indices.contains_key(&vertex) {
            continue;
        }
        // Initialize Tarjan state stack: push the first visit state
        tarjan_stack.push(TarjanState::Visit(vertex.clone()));

        while let Some(state) = tarjan_stack.pop() {
            match state {
                // Phase 1: First visit to vertex u, initialize index and low_link
                TarjanState::Visit(u) => {
                    // Skip if already visited
                    if indices.contains_key(&u) {
                        continue;
                    }
                    // Initialize index and low_link
                    indices.insert(u.clone(), index);
                    low_links.insert(u.clone(), index);
                    index += 1;
                    stack.push(u.clone());
                    on_stack.insert(u.clone());
                    // Push the state for processing adjacent vertices (start from the 0th adjacent vertex)
                    tarjan_stack.push(TarjanState::ProcessNeighbors(u.clone(), 0));
                }

                // Phase 2: Process adjacent vertices of vertex u
                TarjanState::ProcessNeighbors(u, neighbor_idx) => {
                    let neighbors = graph.adj.get(&u).cloned().unwrap_or_default();
                    let num_neighbors = neighbors.len();

                    // Traverse adjacent vertices (start from the current index)
                    if neighbor_idx < num_neighbors {
                        let v = &neighbors[neighbor_idx];
                        // Push the current processing progress back to the stack (process next adjacent vertex next time)
                        tarjan_stack
                            .push(TarjanState::ProcessNeighbors(u.clone(), neighbor_idx + 1));

                        if !indices.contains_key(v) {
                            // Adjacent vertex v is unvisited: process v first, then update u's low_link after processing
                            tarjan_stack.push(TarjanState::UpdateLowLink(u.clone(), v.clone()));
                            tarjan_stack.push(TarjanState::Visit(v.clone()));
                        } else if on_stack.contains(v) {
                            // Adjacent vertex v is on the stack: update u's low_link directly
                            let u_low = low_links[&u];
                            let v_idx = indices[v];
                            low_links.insert(u.clone(), u_low.min(v_idx));
                        }
                    } else {
                        // All adjacent vertices processed, check if it's the root of an SCC
                        let u_idx = indices[&u];
                        let u_low = low_links[&u];

                        if u_low == u_idx {
                            // Pop the stack and generate an SCC
                            let mut scc = HashSet::new();
                            loop {
                                let v = stack.pop().unwrap();
                                on_stack.remove(&v);
                                scc.insert(v.clone());
                                if v == u {
                                    break;
                                }
                            }
                            // Keep only SCCs with at least 2 vertices
                            if scc.len() >= 2 {
                                sccs.push(scc);
                            }
                        }
                    }
                }

                // Phase 3: Backtrack to update low_link (after processing child vertex v)
                TarjanState::UpdateLowLink(u, v) => {
                    if indices.contains_key(&v) && on_stack.contains(&v) {
                        let u_low = low_links[&u];
                        let v_low = low_links[&v];
                        low_links.insert(u.clone(), u_low.min(v_low));
                    }
                }
            }
        }
    }
    sccs
}

/// Szwarcfiter-Lauer algorithm DFS stack state
#[derive(Clone)]
enum DfsState<N>
where
    N: NodeConstraints,
{
    Enter(N, N),                   // (start vertex, current vertex)
    ProcessNeighbors(N, N, usize), // (start vertex, current vertex, neighbor index)
}

/// Non-recursive DFS: core of the Szwarcfiter-Lauer algorithm
fn dfs_find_cycles_non_recursive<N>(
    start: N,
    graph: &CompleteDirectedGraph<N>,
    v_to_idx: &HashMap<N, usize>,
    start_idx: usize,
    cycles: &mut Vec<Vec<N>>,
) where
    N: NodeConstraints,
{
    let mut stack = Vec::new();
    let mut path = Vec::new();
    let mut visited = HashSet::new();

    stack.push(DfsState::Enter(start.clone(), start.clone()));

    while let Some(state) = stack.pop() {
        match state {
            DfsState::Enter(s, current) => {
                if visited.contains(&current) {
                    continue;
                }
                path.push(current.clone());
                visited.insert(current.clone());
                stack.push(DfsState::ProcessNeighbors(s.clone(), current.clone(), 0));
            }

            DfsState::ProcessNeighbors(s, current, neighbor_idx) => {
                let neighbors = graph.adj.get(&current).cloned().unwrap_or_default();
                let num_neighbors = neighbors.len();

                if neighbor_idx < num_neighbors {
                    let neighbor = &neighbors[neighbor_idx];
                    let neighbor_idx_val = v_to_idx[neighbor];

                    if neighbor_idx_val < start_idx {
                        stack.push(DfsState::ProcessNeighbors(
                            s.clone(),
                            current.clone(),
                            neighbor_idx + 1,
                        ));
                        continue;
                    }

                    if neighbor == &s && path.len() >= 2 {
                        cycles.push(path.clone());
                        stack.push(DfsState::ProcessNeighbors(
                            s.clone(),
                            current.clone(),
                            neighbor_idx + 1,
                        ));
                        continue;
                    }

                    if !visited.contains(neighbor) {
                        stack.push(DfsState::ProcessNeighbors(
                            s.clone(),
                            current.clone(),
                            neighbor_idx + 1,
                        ));
                        stack.push(DfsState::Enter(s.clone(), neighbor.clone()));
                    } else {
                        stack.push(DfsState::ProcessNeighbors(
                            s.clone(),
                            current.clone(),
                            neighbor_idx + 1,
                        ));
                    }
                } else {
                    path.pop();
                    visited.remove(&current);
                }
            }
        }
    }
}

/// Find all simple cycles of a directed graph using the
/// Schwarcfiter and Lauer's algorithm.
/// <p/>
/// See:<br/>
/// J.L.Szwarcfiter and P.E.Lauer, Finding the elementary
/// cycles of a directed graph in O(n + m) per cycle,
/// Technical Report Series, #60, May 1974, Univ. of
/// Newcastle upon Tyne, Newcastle upon Tyne, England.
fn szwarcfiter_lauer_cycles<N>(graph: &CompleteDirectedGraph<N>) -> Vec<Vec<N>>
where
    N: NodeConstraints,
{
    let mut cycles = Vec::new();
    let mut graph_copy = graph.clone();
    let sorted_vertices = graph.sorted_vertices();
    let mut v_to_idx = HashMap::new();

    for (idx, v) in sorted_vertices.iter().enumerate() {
        v_to_idx.insert(v.clone(), idx);
    }

    for (s_idx, s) in sorted_vertices.iter().enumerate() {
        // Build subgraph with vertices whose index >= start vertex index
        let subgraph_vertices: HashSet<N> = graph_copy
            .vertices
            .iter()
            .filter(|v| v_to_idx[v] >= s_idx)
            .cloned()
            .collect();
        let subgraph = graph_copy.extract_subgraph(&subgraph_vertices);

        // Find cycles in the subgraph starting from current vertex
        dfs_find_cycles_non_recursive(s.clone(), &subgraph, &v_to_idx, s_idx, &mut cycles);

        // Remove the start vertex from the graph to avoid duplicate cycles
        graph_copy.adj.shift_remove(s);
        graph_copy.vertices.shift_remove(s);
        for (_u, neighbors) in graph_copy.adj.iter_mut() {
            neighbors.retain(|v| v != s);
        }
    }
    cycles
}

/// Integrated logic: first split into SCCs, then enumerate cycles in each SCC (fully non-recursive)
pub fn find_cycles_with_scc<N>(graph: &CompleteDirectedGraph<N>) -> Vec<Vec<N>>
where
    N: NodeConstraints,
{
    let mut all_cycles = Vec::new();
    let sccs = tarjan_scc(graph);
    // Enumerate cycles for each SCC
    for scc in sccs {
        let scc_subgraph = graph.extract_subgraph(&scc);
        // TODO: Parallel execution via tokio-async or rayon
        let scc_cycles = szwarcfiter_lauer_cycles(&scc_subgraph);
        all_cycles.extend(scc_cycles);
    }
    all_cycles
}

#[cfg(test)]
mod tests {
    use crate::algorithm::{CompleteDirectedGraph, find_cycles_with_scc};

    #[test]
    fn test_find_cycle() {
        // Build test graph: contains two SCCs (1->2->3->1) and (4->5->4), with cross-SCC edge 3->4
        let mut graph = CompleteDirectedGraph::new();
        graph.add_edge(1, 2);
        graph.add_edge(2, 3);
        graph.add_edge(3, 1);
        graph.add_edge(4, 5);
        graph.add_edge(5, 4);
        graph.add_edge(3, 4);

        // Find all simple cycles
        let cycles = find_cycles_with_scc(&graph);

        // Print results
        println!("Found elementary cycles:");
        for (i, cycle) in cycles.iter().enumerate() {
            println!("Cycle {}: {:?}", i + 1, cycle);
        }
        assert!(cycles.contains(&vec![1, 2, 3]));
        assert!(cycles.contains(&vec![4, 5]));
        assert_eq!(cycles.len(), 2);
    }
}
