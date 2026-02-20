use criterion::{Criterion, criterion_group, criterion_main};
use directed_graph::analyze::analyze_digraph;
use directed_graph::*;

// Define the benchmark function, consistent with the native logic and adapted to Criterion's API
fn bench_digraph(c: &mut Criterion) {
    // Group benchmarks for easy management
    let mut group = c.benchmark_group("digraph_cycle_detect");
    // Set sample size, larger values mean higher accuracy (default: 100)
    group.sample_size(1000);
    // Measurement time per test (default: 3 seconds)
    group.measurement_time(std::time::Duration::from_secs(10));
    // Flat sampling mode to reduce outliers
    group.sampling_mode(criterion::SamplingMode::Flat);
    // Noise threshold of 5%, ignore minor time fluctuations
    group.noise_threshold(0.05);
    // Extend warm-up time to stabilize CPU cache
    group.warm_up_time(std::time::Duration::from_secs(2));

    // Test 1: Acyclic graph with small scale (10 nodes)
    let mut acyclic_small = DirectedGraph::new();
    for i in 0..10 {
        acyclic_small.add_node(i, vec![i + 1, i + 2]);
    }
    group.bench_function("analyze_digraph_acyclic_small", |b| {
        b.iter(|| analyze_digraph(&acyclic_small))
    });

    // Test 2: Single cycle graph with medium scale (100 nodes)
    let mut single_cycle_mid = DirectedGraph::new();
    for i in 0..100 {
        single_cycle_mid.add_node(i, vec![(i + 1) % 100]);
    }
    group.bench_function("analyze_digraph_single_cycle_mid", |b| {
        b.iter(|| analyze_digraph(&single_cycle_mid))
    });

    // Test 3: Multiple cycles graph with medium scale (50 nodes, 5 independent cycles)
    let mut multi_cycle_mid = DirectedGraph::new();
    for group in 0..5 {
        let start = group * 10;
        for i in start..start + 10 {
            multi_cycle_mid.add_node(i, vec![(i + 1) % 10 + start]);
        }
    }
    group.bench_function("analyze_digraph_multi_cycle_mid", |b| {
        b.iter(|| analyze_digraph(&multi_cycle_mid))
    });

    // Test 4: Acyclic graph with large scale (1000 nodes)
    let mut acyclic_large = DirectedGraph::new();
    for i in 0..1000 {
        acyclic_large.add_node(i, vec![i + 1]);
    }
    group.bench_function("analyze_digraph_acyclic_large", |b| {
        b.iter(|| analyze_digraph(&acyclic_large))
    });

    // Test 5: Complete analysis test - contains single cycle, self-loop and undefined node
    let mut complete_graph = DirectedGraph::new();
    complete_graph.add_node(1, vec![2]);
    complete_graph.add_node(2, vec![3]);
    complete_graph.add_node(3, vec![1]);
    complete_graph.add_node(4, vec![4]);
    complete_graph.add_node(5, vec![6]);
    group.bench_function("analyze_digraph_complete", |b| {
        b.iter(|| analyze_digraph(&complete_graph))
    });

    group.finish(); // Finish the benchmark group
}

// Fixed Criterion syntax: register benchmark group and run
criterion_group!(benches, bench_digraph);
criterion_main!(benches);
