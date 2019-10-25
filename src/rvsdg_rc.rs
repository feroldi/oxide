use std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

#[derive(Clone, Copy, PartialEq, Debug)]
enum PortType {
    State,
    Value,
}

#[derive(Clone, PartialEq, Debug)]
struct Port {
    port_type: PortType,
    label: String,
}

impl Port {
    fn port_type(&self) -> PortType {
        self.port_type
    }
}

#[derive(Debug)]
struct Node {
    ins: Vec<Rc<InData>>,
    outs: Vec<Rc<OutData>>,
}

#[derive(Debug)]
struct InData {
    origin: Out,
    port: Port,
}

impl InData {
    fn with_origin(port: Port, origin: Out) -> Rc<InData> {
        assert_eq!(
            port.port_type(),
            origin.port_type(),
            "incompatible port types"
        );

        let input_data = Rc::new(InData {
            origin: origin.clone(),
            port,
        });

        let mut origin_mut = origin;
        origin_mut.add_user(In::Simple {
            data: input_data.clone(),
        });

        input_data
    }
}

#[derive(Clone, Debug)]
enum In {
    Simple { data: Rc<InData> },
}

impl In {
    fn port_type(&self) -> PortType {
        match self {
            In::Simple { data } => data.port.port_type(),
        }
    }

    fn origin(&self) -> Out {
        match self {
            In::Simple { data } => data.origin.clone(),
        }
    }
}

#[derive(Clone, Debug)]
enum WeakIn {
    Simple { data: Weak<InData> },
}

#[derive(Debug)]
struct OutData {
    users: RefCell<Vec<WeakIn>>,
    port: Port,
}

impl OutData {
    fn new(port: Port) -> Rc<OutData> {
        let output_data = Rc::new(OutData {
            users: RefCell::default(),
            port,
        });

        output_data
    }
}

#[derive(Clone, Debug)]
enum Out {
    Simple { data: Rc<OutData> },
}

impl Out {
    fn users(&self) -> impl Iterator<Item = In> {
        match self {
            Out::Simple { data: out_data } => {
                out_data
                    .users
                    .borrow()
                    .clone()
                    .into_iter()
                    .flat_map(|input| match input {
                        WeakIn::Simple { data: weak_in_data } => match weak_in_data.upgrade() {
                            Some(in_data) => Some(In::Simple { data: in_data }),
                            None => None,
                        },
                    })
            }
        }
    }

    fn add_user(&mut self, user: In) {
        match self {
            Out::Simple { data: out_data } => match user {
                In::Simple { data: user_data } => {
                    out_data.users.borrow_mut().push(WeakIn::Simple {
                        data: Rc::downgrade(&user_data),
                    })
                }
            },
        }
    }

    fn port_type(&self) -> PortType {
        match self {
            Out::Simple { data } => data.port.port_type(),
        }
    }
}

impl PartialEq for In {
    fn eq(&self, other: &In) -> bool {
        match (self, other) {
            (In::Simple { data: lhs }, In::Simple { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
        }
    }
}

impl PartialEq for Out {
    fn eq(&self, other: &Out) -> bool {
        match (self, other) {
            (Out::Simple { data: lhs }, Out::Simple { data: rhs }) => Rc::ptr_eq(&lhs, &rhs),
        }
    }
}

impl Node {
    fn new() -> Node {
        Node {
            ins: Vec::new(),
            outs: Vec::new(),
        }
    }

    fn add_input(&mut self, port_type: PortType, origin: Out) -> In {
        let port = Port {
            port_type,
            label: format!("i{}", self.ins.len()),
        };
        let input_data = InData::with_origin(port, origin);
        self.ins.push(input_data.clone());

        In::Simple { data: input_data }
    }

    fn add_output(&mut self, port_type: PortType) -> Out {
        let port = Port {
            port_type,
            label: format!("o{}", self.outs.len()),
        };
        let output_data = OutData::new(port);
        self.outs.push(output_data.clone());

        Out::Simple { data: output_data }
    }
}

#[cfg(test)]
mod tests {
    use super::{Node, PortType};

    #[test]
    fn create_node() {
        let n0 = Node::new();

        assert_eq!(0, n0.ins.len());
        assert_eq!(0, n0.outs.len());
    }

    #[test]
    fn create_nodes_with_ports() {
        let mut n0 = Node::new();
        let o0 = n0.add_output(PortType::Value);

        assert_eq!(PortType::Value, o0.port_type());

        assert_eq!(0, n0.ins.len());
        assert_eq!(1, n0.outs.len());

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortType::Value, o0.clone());
        let i1 = n1.add_input(PortType::Value, o0.clone());

        assert_eq!(PortType::Value, i0.port_type());
        assert_eq!(PortType::Value, i1.port_type());

        assert_eq!(2, n1.ins.len());
        assert_eq!(0, n1.outs.len());

        let mut users = o0.users();

        assert_eq!(Some(i0), users.next());
        assert_eq!(Some(i1), users.next());
        assert_eq!(None, users.next());
    }

    #[test]
    #[should_panic = "incompatible port types"]
    fn create_nodes_with_wrong_port_type() {
        let mut n0 = Node::new();
        let o0 = n0.add_output(PortType::Value);

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortType::State, o0.clone());

        assert_eq!(o0, i0.origin());
    }
}
