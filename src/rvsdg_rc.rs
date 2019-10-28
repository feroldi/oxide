use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

#[derive(Clone, Copy, PartialEq, Debug)]
enum PortTy {
    State,
    Value,
}

#[derive(Clone, PartialEq, Debug)]
struct Port {
    ty: PortTy,
    label: String,
}

impl Port {
    fn ty(&self) -> PortTy {
        self.ty
    }
}

#[derive(Debug)]
struct NodeData {
    ins: Vec<Rc<InData>>,
    outs: Vec<Rc<OutData>>,
}

#[derive(Clone, Debug)]
struct Node {
    data: Rc<RefCell<NodeData>>,
}

impl PartialEq for Node {
    fn eq(&self, other: &Node) -> bool {
        Rc::ptr_eq(&self.data, &other.data)
    }
}

impl Node {
    fn new() -> Node {
        Node {
            data: Rc::new(RefCell::new(NodeData {
                ins: Vec::new(),
                outs: Vec::new(),
            })),
        }
    }

    fn add_input(&mut self, port_ty: PortTy, origin: Out) -> In {
        let port = Port {
            ty: port_ty,
            label: format!("i{}", self.data.borrow().ins.len()),
        };
        let input_data = InData::with_origin(self.clone(), port, origin);
        self.data.borrow_mut().ins.push(input_data.clone());

        In::Simple { data: input_data }
    }

    fn add_output(&mut self, port_ty: PortTy) -> Out {
        let port = Port {
            ty: port_ty,
            label: format!("o{}", self.data.borrow().outs.len()),
        };
        let output_data = OutData::new(self.clone(), port);
        self.data.borrow_mut().outs.push(output_data.clone());

        Out::Simple { data: output_data }
    }

    fn inputs_len(&self) -> usize {
        self.data.borrow().ins.len()
    }

    fn outputs_len(&self) -> usize {
        self.data.borrow().outs.len()
    }
}

#[derive(Debug)]
struct InData {
    origin: Out,
    port: Port,
    consumer: Weak<RefCell<NodeData>>,
}

impl Into<In> for Rc<InData> {
    fn into(self) -> In {
        In::Simple { data: self }
    }
}

impl InData {
    fn with_origin(consumer: Node, port: Port, origin: Out) -> Rc<InData> {
        assert_eq!(port.ty(), origin.ty(), "incompatible port types");

        let input_data = Rc::new(InData {
            origin: origin.clone(),
            port,
            consumer: Rc::downgrade(&consumer.data),
        });

        let mut origin_mut = origin;
        origin_mut.add_user(In::Simple {
            data: input_data.clone(),
        });

        input_data
    }

    fn consumer(&self) -> Option<Node> {
        self.consumer.upgrade().map(|data| Node { data })
    }
}

#[derive(Debug)]
struct RegionData {
    ress: Vec<Rc<ResData>>,
    args: Vec<Rc<ArgData>>,
}

#[derive(Clone, Debug)]
struct Region {
    data: Rc<RefCell<RegionData>>,
}

impl Region {
    fn new() -> Region {
        Region {
            data: Rc::new(RefCell::new(RegionData {
                ress: vec![],
                args: vec![],
            })),
        }
    }

    fn add_result(&mut self, output_map: Out, port_ty: PortTy, origin: Out) -> In {
        let port = Port {
            ty: port_ty,
            label: format!("r{}", self.data.borrow().ress.len()),
        };

        let output_data = match output_map {
            Out::Simple { data } => data,
            _ => panic!("output_map should be a simple output"),
        };

        let result_data = ResData::with_origin(self.clone(), output_data, port, origin);
        self.data.borrow_mut().ress.push(result_data.clone());

        In::Region { data: result_data }
    }

    fn add_argument(&mut self, input_map: In, port_ty: PortTy) -> Out {
        let port = Port {
            ty: port_ty,
            label: format!("a{}", self.data.borrow().args.len()),
        };

        let input_data = match input_map {
            In::Simple { data } => data,
            _ => panic!("input_map should be a simple input"),
        };

        let argument_data = ArgData::new(self.clone(), input_data, port);
        self.data.borrow_mut().args.push(argument_data.clone());

        Out::Region {
            data: argument_data,
        }
    }
}

#[derive(Debug)]
struct ResData {
    port: Port,
    origin: Out,
    output_map: Weak<OutData>,
    region: Weak<RefCell<RegionData>>,
}

impl ResData {
    fn with_origin(
        region: Region,
        output_map: Rc<OutData>,
        port: Port,
        origin: Out,
    ) -> Rc<ResData> {
        assert_eq!(output_map.port.ty(), origin.ty(), "incompatible port types");
        assert_eq!(port.ty(), origin.ty(), "incompatible port types");

        let result_data = Rc::new(ResData {
            port,
            origin: origin.clone(),
            output_map: Rc::downgrade(&output_map),
            region: Rc::downgrade(&region.data),
        });

        let mut origin_mut = origin;
        origin_mut.add_user(In::Region {
            data: result_data.clone(),
        });

        result_data
    }

    fn region(&self) -> Option<Region> {
        self.region.upgrade().map(|data| Region { data })
    }
}

#[derive(Debug)]
struct ArgData {
    users: RefCell<Vec<WeakIn>>,
    port: Port,
    input_map: Weak<InData>,
    region: Weak<RefCell<RegionData>>,
}

impl ArgData {
    fn new(region: Region, input_map: Rc<InData>, port: Port) -> Rc<ArgData> {
        let argument_data = Rc::new(ArgData {
            users: RefCell::default(),
            port,
            input_map: Rc::downgrade(&input_map),
            region: Rc::downgrade(&region.data),
        });

        argument_data
    }

    fn input_map(&self) -> Option<Rc<InData>> {
        self.input_map.upgrade()
    }

    fn region(&self) -> Option<Region> {
        self.region.upgrade().map(|data| Region { data })
    }
}

#[derive(Clone, Debug)]
enum In {
    Simple { data: Rc<InData> },
    Region { data: Rc<ResData> },
}

impl In {
    fn ty(&self) -> PortTy {
        match self {
            In::Simple { data } => data.port.ty(),
            In::Region { data } => data.port.ty(),
        }
    }

    fn origin(&self) -> Out {
        match self {
            In::Simple { data } => data.origin.clone(),
            In::Region { data } => data.origin.clone(),
        }
    }

    fn consumer(&self) -> Option<Node> {
        match self {
            In::Simple { data } => data.consumer(),
            In::Region { .. } => None,
        }
    }

    fn output_map(&self) -> Option<Out> {
        match self {
            In::Region { data } => data.output_map.upgrade().map(|out| out.into()),
            In::Simple { .. } => None,
        }
    }

    fn as_in(&self) -> Option<Rc<InData>> {
        match self {
            In::Simple { data } => Some(data.clone()),
            _ => None,
        }
    }

    fn as_res(&self) -> Option<Rc<ResData>> {
        match self {
            In::Region { data } => Some(data.clone()),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
enum WeakIn {
    Simple { data: Weak<InData> },
    Region { data: Weak<ResData> },
}

impl WeakIn {
    fn upgrade(&self) -> Option<In> {
        match self {
            WeakIn::Simple { data } => data.upgrade().map(|data| In::Simple { data }),
            WeakIn::Region { data } => data.upgrade().map(|data| In::Region { data }),
        }
    }
}

#[derive(Debug)]
struct OutData {
    users: RefCell<Vec<WeakIn>>,
    port: Port,
    producer: Weak<RefCell<NodeData>>,
}

impl Into<Out> for Rc<OutData> {
    fn into(self) -> Out {
        Out::Simple { data: self }
    }
}

impl OutData {
    fn new(node: Node, port: Port) -> Rc<OutData> {
        let output_data = Rc::new(OutData {
            users: RefCell::default(),
            port,
            producer: Rc::downgrade(&node.data),
        });

        output_data
    }

    fn producer(&self) -> Option<Node> {
        self.producer.upgrade().map(|data| Node { data })
    }
}

#[derive(Clone, Debug)]
enum Out {
    Simple { data: Rc<OutData> },
    Region { data: Rc<ArgData> },
}

impl Out {
    fn users(&self) -> impl Iterator<Item = In> {
        let users = match self {
            Out::Simple { data } => data.users.borrow(),
            Out::Region { data } => data.users.borrow(),
        };

        users.clone().into_iter().flat_map(|input| input.upgrade())
    }

    fn add_user(&mut self, user: In) {
        let mut users = match self {
            Out::Simple { data } => data.users.borrow_mut(),
            Out::Region { data } => data.users.borrow_mut(),
        };

        match user {
            In::Simple { data: user_data } => users.push(WeakIn::Simple {
                data: Rc::downgrade(&user_data),
            }),
            In::Region { data: user_data } => users.push(WeakIn::Region {
                data: Rc::downgrade(&user_data),
            }),
        }
    }

    fn ty(&self) -> PortTy {
        match self {
            Out::Simple { data } => data.port.ty(),
            Out::Region { data } => data.port.ty(),
        }
    }

    fn producer(&self) -> Option<Node> {
        match self {
            Out::Simple { data } => data.producer(),
            _ => None,
        }
    }

    fn region(&self) -> Option<Region> {
        match self {
            Out::Region { data } => data.region(),
            _ => None,
        }
    }

    fn input_map(&self) -> Option<In> {
        match self {
            Out::Region { data } => data.input_map.upgrade().map(|input| input.into()),
            _ => None,
        }
    }

    fn as_out(&self) -> Option<Rc<OutData>> {
        match self {
            Out::Simple { data } => Some(data.clone()),
            _ => None,
        }
    }

    fn as_arg(&self) -> Option<Rc<ArgData>> {
        match self {
            Out::Region { data } => Some(data.clone()),
            _ => None,
        }
    }
}

impl PartialEq for In {
    fn eq(&self, other: &In) -> bool {
        match (self, other) {
            (In::Simple { data: lhs }, In::Simple { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
            (In::Region { data: lhs }, In::Region { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
            (In::Simple { .. }, In::Region { .. }) => false,
            (In::Region { .. }, In::Simple { .. }) => false,
        }
    }
}

impl PartialEq for Out {
    fn eq(&self, other: &Out) -> bool {
        match (self, other) {
            (Out::Simple { data: lhs }, Out::Simple { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
            (Out::Region { data: lhs }, Out::Region { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
            (Out::Simple { .. }, Out::Region { .. }) => false,
            (Out::Region { .. }, Out::Simple { .. }) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, PortTy, Region};

    #[test]
    fn create_node() {
        let n0 = Node::new();

        assert_eq!(0, n0.inputs_len());
        assert_eq!(0, n0.outputs_len());
    }

    #[test]
    fn create_nodes_with_ports() {
        let mut n0 = Node::new();
        let o0 = n0.add_output(PortTy::Value);

        assert_eq!(PortTy::Value, o0.ty());

        assert_eq!(0, n0.inputs_len());
        assert_eq!(1, n0.outputs_len());

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortTy::Value, o0.clone());
        let i1 = n1.add_input(PortTy::Value, o0.clone());

        assert_eq!(PortTy::Value, i0.ty());
        assert_eq!(PortTy::Value, i1.ty());

        assert_eq!(2, n1.inputs_len());
        assert_eq!(0, n1.outputs_len());

        let mut users = o0.users();

        assert_eq!(Some(i0), users.next());
        assert_eq!(Some(i1), users.next());
        assert_eq!(None, users.next());
    }

    #[test]
    #[should_panic = "incompatible port types"]
    fn create_nodes_with_wrong_port_type() {
        let mut n0 = Node::new();
        let o0 = n0.add_output(PortTy::Value);

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortTy::State, o0.clone());

        assert_eq!(o0, i0.origin());
    }

    #[test]
    fn producer_and_consumer() {
        let mut n0 = Node::new();
        let output = n0.add_output(PortTy::Value);

        assert_eq!(Some(&n0), output.producer().as_ref());

        let mut n1 = Node::new();
        let input = n1.add_input(PortTy::Value, output.clone());

        assert_eq!(Some(&n1), input.consumer().as_ref());
        assert_eq!(Some(&n0), input.origin().producer().as_ref());
        assert_eq!(
            Some(&n1),
            output
                .users()
                .next()
                .and_then(|user| user.consumer())
                .as_ref()
        );
    }

    #[test]
    fn nodes_inside_region() {
        let mut n0 = Node::new();
        let n0_o0 = n0.add_output(PortTy::Value);
        assert_eq!(Some(&n0), n0_o0.producer().as_ref());

        let mut n1 = Node::new();

        let n1_i0 = n1.add_input(PortTy::Value, n0_o0.clone());
        assert_eq!(n0_o0, n1_i0.origin());

        let n1_o0 = n1.add_output(PortTy::Value);
        assert_eq!(Some(&n1), n1_o0.producer().as_ref());

        let mut r0 = Region::new();
        let r0_a0 = r0.add_argument(n1_i0.clone(), PortTy::Value);

        assert_eq!(Some(&n1_i0), r0_a0.input_map().as_ref());

        let mut n2 = Node::new();
        let n2_i0 = n2.add_input(PortTy::Value, r0_a0.clone());
        assert_eq!(r0_a0, n2_i0.origin());

        let n2_o0 = n2.add_output(PortTy::Value);
        assert_eq!(Some(&n2), n2_o0.producer().as_ref());

        let r0_r0 = r0.add_result(n1_o0.clone(), PortTy::Value, n2_o0.clone());
        assert_eq!(n2_o0, r0_r0.origin());
        assert_eq!(Some(&n1_o0), r0_r0.output_map().as_ref());
    }
}
