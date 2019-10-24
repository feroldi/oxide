use std::convert::Into;

#[derive(PartialEq, Debug)]
enum PortType {
    State,
    Value,
}

struct InPort {
    port_type: PortType,
    port_index: usize,
}

struct OutPort {
    port_type: PortType,
    port_index: usize,
}

struct BasicNodeData {
    first_edge: Option<EdgeIndex>,
    operation: Box<dyn Operation>,
}

enum ComplexNodeKind {
    Omega,
    Phi,
    Lambda,
    Theta,
    Gamma,
}

struct ComplexNodeData {
    first_edge: Option<EdgeIndex>,
    first_region: Option<RegionIndex>,
    kind: ComplexNodeKind,
}

struct RegionData {
    first_edge: Option<EdgeIndex>,
    next_region: Option<RegionIndex>,
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct BasicNodeIndex(usize);

#[derive(PartialEq, Debug)]
struct ComplexNodeIndex(usize);

struct RegionIndex(usize);

enum NodeIndex {
    Basic(BasicNodeIndex),
    Complex(ComplexNodeIndex),
    Region(RegionIndex),
}

impl Into<NodeIndex> for BasicNodeIndex {
    fn into(self) -> NodeIndex {
        NodeIndex::Basic(self)
    }
}

impl Into<NodeIndex> for ComplexNodeIndex {
    fn into(self) -> NodeIndex {
        NodeIndex::Complex(self)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct EdgeIndex(usize);

struct EdgeData {
    output: Out,
    input: In,
    next_edge: Option<EdgeIndex>,
}

struct In {
    port: InPort,
    node_index: NodeIndex,
}

struct Out {
    port: OutPort,
    node_index: NodeIndex,
}

struct Graph {
    basic_nodes: Vec<BasicNodeData>,
    complex_nodes: Vec<ComplexNodeData>,
    regions: Vec<RegionData>,
    edges: Vec<EdgeData>,
}

impl Graph {
    fn new() -> Graph {
        Graph {
            basic_nodes: vec![],
            complex_nodes: vec![],
            regions: vec![],
            edges: vec![],
        }
    }

    fn create_basic_node(&mut self, operation: impl Operation + 'static) -> BasicNodeIndex {
        self.basic_nodes.push(BasicNodeData {
            first_edge: None,
            operation: Box::new(operation),
        });
        let index = self.basic_nodes.len() - 1;
        BasicNodeIndex(index)
    }

    fn create_complex_node(&mut self, kind: ComplexNodeKind) -> ComplexNodeIndex {
        self.complex_nodes.push(ComplexNodeData {
            first_edge: None,
            first_region: None,
            kind,
        });
        let index = self.complex_nodes.len() - 1;
        ComplexNodeIndex(index)
    }

    fn next_edge(&self, edge_index: EdgeIndex) -> Option<EdgeIndex> {
        self.edges[edge_index.0].next_edge
    }

    fn connect_ports(&mut self, input: In, output: Out) -> EdgeIndex {
        assert_eq!(
            output.port.port_type, input.port.port_type,
            "incompatible port types"
        );

        let edge_index = EdgeIndex(self.edges.len());

        let next_edge = match input.node_index {
            NodeIndex::Basic(BasicNodeIndex(index)) => {
                self.basic_nodes[index].first_edge.replace(edge_index)
            }
            NodeIndex::Complex(ComplexNodeIndex(index)) => {
                self.complex_nodes[index].first_edge.replace(edge_index)
            }
            NodeIndex::Region(RegionIndex(index)) => {
                self.regions[index].first_edge.replace(edge_index)
            }
        };

        self.edges.push(EdgeData {
            output,
            input,
            next_edge,
        });

        edge_index
    }

    fn basic_input(&self, basic_node_id: BasicNodeIndex, port_index: usize) -> In {
        let port = self.basic_nodes[basic_node_id.0]
            .operation
            .input(port_index);
        In {
            port,
            node_index: basic_node_id.into(),
        }
    }

    fn basic_output(&self, basic_node_id: BasicNodeIndex, port_index: usize) -> Out {
        let port = self.basic_nodes[basic_node_id.0]
            .operation
            .output(port_index);
        Out {
            port,
            node_index: basic_node_id.into(),
        }
    }

    fn complex_input(
        &self,
        complex_node_id: ComplexNodeIndex,
        port_type: PortType,
        port_index: usize,
    ) -> In {
        In {
            port: InPort {
                port_type,
                port_index,
            },
            node_index: complex_node_id.into(),
        }
    }

    fn complex_output(
        &self,
        complex_node_id: ComplexNodeIndex,
        port_type: PortType,
        port_index: usize,
    ) -> Out {
        Out {
            port: OutPort {
                port_type,
                port_index,
            },
            node_index: complex_node_id.into(),
        }
    }
}

trait Operation {
    fn input(&self, port_index: usize) -> InPort;
    fn output(&self, port_index: usize) -> OutPort;
}

mod ir {
    use super::{InPort, Operation, OutPort, PortType};

    pub(crate) struct ConstI32 {
        pub(crate) val: i32,
    }

    impl Operation for ConstI32 {
        fn input(&self, port_index: usize) -> InPort {
            unreachable!()
        }

        fn output(&self, port_index: usize) -> OutPort {
            assert_eq!(0, port_index);
            OutPort {
                port_type: PortType::Value,
                port_index: 0,
            }
        }
    }

    pub(crate) struct BinAddI32;

    impl Operation for BinAddI32 {
        fn input(&self, port_index: usize) -> InPort {
            if port_index < 2 {
                InPort {
                    port_type: PortType::Value,
                    port_index,
                }
            } else {
                unreachable!()
            }
        }

        fn output(&self, port_index: usize) -> OutPort {
            assert_eq!(0, port_index);
            OutPort {
                port_type: PortType::Value,
                port_index: 0,
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{ir, BasicNodeIndex, ComplexNodeIndex, ComplexNodeKind, Graph, PortType};

    #[test]
    fn create_basic_node() {
        let mut graph = Graph::new();
        let n0 = graph.create_basic_node(ir::BinAddI32);
        let n1 = graph.create_basic_node(ir::BinAddI32);

        assert_eq!(BasicNodeIndex(0), n0);
        assert_eq!(BasicNodeIndex(1), n1);
    }

    #[test]
    fn connect_basic_node_ports() {
        let mut graph = Graph::new();
        let n_add = graph.create_basic_node(ir::BinAddI32);
        let n_sub = graph.create_basic_node(ir::BinAddI32);
        let n_2 = graph.create_basic_node(ir::ConstI32 { val: 2 });
        let n_3 = graph.create_basic_node(ir::ConstI32 { val: 3 });

        let e_add_2 = graph.connect_ports(graph.basic_input(n_add, 0), graph.basic_output(n_2, 0));

        let e_add_3 = graph.connect_ports(graph.basic_input(n_add, 1), graph.basic_output(n_3, 0));

        let e_sub_2 = graph.connect_ports(graph.basic_input(n_sub, 0), graph.basic_output(n_2, 0));

        let e_sub_3 = graph.connect_ports(graph.basic_input(n_sub, 1), graph.basic_output(n_3, 0));

        assert_eq!(Some(e_add_2), graph.next_edge(e_add_3));
        assert_eq!(None, graph.next_edge(e_add_2));

        assert_eq!(Some(e_sub_2), graph.next_edge(e_sub_3));
        assert_eq!(None, graph.next_edge(e_sub_2));
    }

    #[test]
    #[should_panic]
    fn index_bin_add_i32_outport_out_of_bounds() {
        let mut graph = Graph::new();
        let node = graph.create_basic_node(ir::BinAddI32);
        let _ = graph.basic_output(node, 1);
    }

    #[test]
    fn create_complex_node() {
        let mut graph = Graph::new();
        let n0 = graph.create_complex_node(ComplexNodeKind::Omega);
        let n1 = graph.create_complex_node(ComplexNodeKind::Gamma);

        assert_eq!(ComplexNodeIndex(0), n0);
        assert_eq!(ComplexNodeIndex(1), n1);
    }

    #[test]
    fn connect_complex_node_ports() {
        let mut graph = Graph::new();
        let n0 = graph.create_basic_node(ir::ConstI32 { val: 42 });
        let n1 = graph.create_basic_node(ir::BinAddI32);
        let gamma = graph.create_complex_node(ComplexNodeKind::Gamma);

        let edge = graph.connect_ports(
            graph.complex_input(gamma, PortType::Value, 0),
            graph.basic_output(n0, 0),
        );

        assert_eq!(None, graph.next_edge(edge));
    }
}
