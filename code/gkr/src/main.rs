use std::{
    array,
    fmt::{self, Debug},
};

use petgraph::{
    dot::{Config, Dot},
    graph::{DiGraph, NodeIndex},
};

/// A wire is uniquely identified from its node-id and slot_id
#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash)]
pub struct Wire {
    /// The wire ID
    pub(crate) id: usize,
    /// The node identifier of the incoming gate
    pub(crate) node_idx: NodeIndex,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// GateType([Input_1, ..., Input_n], Output, AssociatedData)
pub(crate) enum GateType {
    // Scalar Field
    Witness((), Wire),
    Output([Wire; 1], ()),
    Print([Wire; 1], (), (&'static str, &'static str)),
    Add([Wire; 2], Wire),
    Multiply([Wire; 2], Wire),
}
impl fmt::Display for GateType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone)]
pub struct CircuitSpec {
    pub(crate) graph: DiGraph<GateType, Wire>,
    pub(crate) witness_wire_count: usize,
    pub(crate) output_wire_count: usize,
    pub(crate) wire_count: usize,
}

impl CircuitSpec {
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            witness_wire_count: 0,
            output_wire_count: 0,
            wire_count: 0,
        }
    }

    // WARNING: This might be dangerous if the petgraph crate changes its internals
    fn next_node_index(&self) -> NodeIndex {
        let node_index: NodeIndex = NodeIndex::new(self.graph.node_count());
        node_index
    }

    fn new_wire(&mut self) -> Wire {
        let id = self.wire_count;
        let node_idx = self.next_node_index();
        self.wire_count += 1;
        Wire { id, node_idx }
    }

    pub fn witness(&mut self) -> Wire {
        let out_wire = self.new_wire();
        self.graph.add_node(GateType::Witness((), out_wire));
        out_wire
    }

    pub fn add_gate(&mut self, left: Wire, right: Wire) -> Wire {
        let in_wires = [left, right];
        let out_wire = self.new_wire();

        let node = self.graph.add_node(GateType::Add(in_wires, out_wire));

        self.graph.add_edge(left.node_idx, node, left);
        self.graph.add_edge(right.node_idx, node, right);

        out_wire
    }

    pub fn mul_gate(&mut self, left: Wire, right: Wire) -> Wire {
        let in_wires = [left, right];
        let out_wire = self.new_wire();

        let node = self.graph.add_node(GateType::Multiply(in_wires, out_wire));
        self.graph.add_edge(left.node_idx, node, left);
        self.graph.add_edge(right.node_idx, node, right);

        out_wire
    }

    pub fn output_gate(&mut self, input: Wire) {
        let node = self.graph.add_node(GateType::Output([input], ()));
        self.graph.add_edge(input.node_idx, node, input);
    }

    pub fn print(&mut self, input: Wire, label_1: &'static str, label_2: &'static str) {
        let node = self
            .graph
            .add_node(GateType::Print([input], (), (label_1, label_2)));
        self.graph.add_edge(input.node_idx, node, input);
    }
}

fn main() {
    println!("Hello, world!");
}
