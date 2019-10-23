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
    fn with_label(port_type: PortType, label: String) -> Port {
        Port { port_type, label }
    }

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

#[derive(Clone, Debug)]
struct In {
    data: Rc<InData>,
}

impl In {
    fn with_origin(port: Port, origin: Out) -> In {
        assert_eq!(
            port.port_type(),
            origin.port_type(),
            "incompatible port types"
        );

        let input_data = Rc::new(InData {
            origin: origin.clone(),
            port,
        });

        let input = In { data: input_data };
        let mut origin_mut = origin;
        origin_mut.add_user(input.clone());

        input
    }

    fn port_type(&self) -> PortType {
        self.data.port.port_type()
    }

    fn origin(&self) -> Out {
        self.data.origin.clone()
    }
}

#[derive(Debug)]
struct OutData {
    users: RefCell<Vec<Weak<InData>>>,
    port: Port,
}

#[derive(Clone, Debug)]
struct Out {
    data: Rc<OutData>,
}

impl Out {
    fn new(port: Port) -> Out {
        let output_data = Rc::new(OutData {
            users: RefCell::default(),
            port,
        });

        Out { data: output_data }
    }

    fn users(&self) -> impl Iterator<Item = In> {
        self.data
            .users
            .borrow()
            .clone()
            .into_iter()
            .flat_map(|input| input.upgrade().and_then(|data| Some(In { data })))
    }

    fn add_user(&mut self, user: In) {
        self.data.users.borrow_mut().push(Rc::downgrade(&user.data));
    }

    fn port_type(&self) -> PortType {
        self.data.port.port_type()
    }
}

impl PartialEq for In {
    fn eq(&self, other: &In) -> bool {
        Rc::ptr_eq(&self.data, &other.data)
    }
}

impl PartialEq for Out {
    fn eq(&self, other: &Out) -> bool {
        Rc::ptr_eq(&self.data, &other.data)
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
        let port = Port::with_label(port_type, format!("i{}", self.ins.len()));
        let input = In::with_origin(port, origin);
        self.ins.push(input.data.clone());
        input
    }

    fn add_output(&mut self, port_type: PortType) -> Out {
        let port = Port::with_label(port_type, format!("o{}", self.outs.len()));
        let output = Out::new(port);
        self.outs.push(output.data.clone());
        output
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
