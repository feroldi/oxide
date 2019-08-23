use std::collections::HashMap;

struct Interned<'ncx, T: ?Sized>(&'ncx T);

enum NodeKind<'ncx> {
    Binary(Operator, Node<'ncx>, Node<'ncx>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PortType {
    Value,
    State,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct InputPort {
    port_type: PortType,
    origin: OutputPort,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct OutputPort<'a> {
    port_type: PortType,
    index: usize,
    producer: NodeRef<'a>,
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

/// Signature of a node.
#[derive(Copy, Clone, PartialEq, Eq)]
struct Sig {
    val_ins: usize,
    val_outs: usize,
    st_ins: usize,
    st_outs: usize,
}

type Node<'ncx> = &'ncx NodeS<'ncx>;

#[derive(Copy, Clone, PartialEq, Eq)]
struct ValIn<'ncx> {
    index: usize,
    origin: Node<'ncx>,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum BinOp {
    Add,
    Sub,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum UnOp {
    Neg,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum NodeKind<'ncx> {
    Lit(u128),
    Unary(UnOp, ValIn<'ncx>),
    Bin(BinOp, ValIn<'ncx>, ValIn<'ncx>),
}

struct NodeS<'ncx> {
    kind: NodeKind<'ncx>,
}

struct NodeCtxt<'ncx> {

}

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
        let next_node_id = self.compute_next_node_id();
        let node_id = *self.lit_nodes.entry(lit_value).or_insert(next_node_id);

        if node_id == next_node_id {
            self.nodes.push(NodeData {
                inputs: Vec::new(),
                outputs: vec![OutputPort {
                    port_type: PortType::Value,
                }],
                operator: Operator::Lit(lit_value),
            });
        }

        NodeRef {
            graph: self,
            node_id,
        }
    }

    // TODO: check if both operands type-match.
    /// Creates a binary ADD operation node with `lhs` and `rhs` as operands.
    fn create_add<'a>(&'a mut self, lhs: NodeRef<'a>, rhs: NodeRef<'a>) -> NodeRef<'a> {
        let add_node_data = NodeData {
            inputs: vec![
                InputPort {
                    port_type: PortType::Value,
                    origin: lhs.value_output(0),
                },
                InputPort {
                    port_type: PortType::Value,
                    origin: rhs.value_output(0),
                },
            ],
            outputs: vec![OutputPort {
                port_type: PortType::Value,
            }],
            operator: Operator::BinAdd,
        };

        let node_id = self.push_node(add_node_data);

        NodeRef {
            graph: self,
            node_id,
        }
    }

    fn compute_next_node_id(&self) -> NodeId {
        NodeId(self.nodes.len())
    }

    fn push_node(&mut self, node_data: NodeData) -> NodeId {
        let next_node_id = self.compute_next_node_id();
        self.nodes.push(node_data);
        next_node_id
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
