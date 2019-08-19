use std::collections::HashMap;

#[derive(Clone, Copy, PartialEq, Eq)]
enum PortType {
    Value,
    State,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct InputPort {
    kind: PortType,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct OutputPort {
    kind: PortType,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Operator {
    Lit(u64),
    BinAdd,
    BinSub,
    BinMul,
    BinDiv,
    Neg,
}

struct NodeData {
    inputs: Vec<InputPort>,
    outputs: Vec<OutputPort>,
    operator: Operator,
}

struct NodeRef<'a> {
    graph: &'a Graph,
    node_id: NodeId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct NodeId(usize);

struct Graph {
    lit_nodes: HashMap<u64, NodeId>,
    nodes: Vec<NodeData>,
}

impl Graph {
    fn new() -> Graph {
        Graph {
            lit_nodes: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    /// Returns a literal value node. This reuses a pre-existing node based on
    /// its value, or the node is created if none exists.
    fn get_lit<'a>(&'a mut self, lit_value: u64) -> NodeRef<'a> {
        let next_node_id = NodeId(self.nodes.len());
        let node_id = *self.lit_nodes.entry(lit_value).or_insert(next_node_id);

        if node_id == next_node_id {
            self.nodes.push(NodeData {
                inputs: Vec::new(),
                outputs: vec![OutputPort {
                    kind: PortType::Value,
                }],
                operator: Operator::Lit(lit_value),
            });
        }

        NodeRef {
            graph: self,
            node_id,
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Graph, NodeId};

    #[test]
    fn create_lit_and_reuse_pre_existing_based_on_value() {
        let mut graph = Graph::new();

        let lit_a = graph.get_lit(42);
        assert_eq!(NodeId(0), lit_a.node_id);

        let lit_b = graph.get_lit(314);
        assert_eq!(NodeId(1), lit_b.node_id);

        let lit_c = graph.get_lit(42);
        assert_eq!(NodeId(0), lit_c.node_id);
    }
}
