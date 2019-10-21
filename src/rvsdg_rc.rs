use std::{
    cell::RefCell,
    fmt::{self, Debug},
    rc::Rc,
};

trait SimpleOp {
    fn operand(&self, index: usize) -> Port;
    fn result(&self, index: usize) -> Port;
}

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

struct Node {
    ins: Vec<In>,
    outs: Vec<Out>,
}

struct InData {
    origin: Out,
    port: Port,
}

#[derive(Clone)]
struct In {
    data: Rc<RefCell<InData>>,
}

impl In {
    fn with_origin(port: Port, origin: Out) -> In {
        assert_eq!(port.port_type, origin.port_type(), "incompatible port types");

        let input_data = Rc::new(RefCell::new(InData {
            origin: origin.clone(),
            port,
        }));

        let input = In { data: input_data };
        let mut origin_mut = origin;
        origin_mut.add_user(input.clone());

        input
    }
}

struct OutData {
    users: Vec<In>,
    port: Port,
}

#[derive(Clone)]
struct Out {
    data: Rc<RefCell<OutData>>,
}

impl Out {
    fn new(port: Port) -> Out {
        let output_data = Rc::new(RefCell::new(OutData {
            users: Vec::new(),
            port,
        }));

        Out { data: output_data }
    }

    fn users(&self) -> impl Iterator<Item = In> {
        self.data.borrow().users.clone().into_iter()
    }

    fn add_user(&mut self, user: In) {
        self.data.borrow_mut().users.push(user);
    }

    fn port_type(&self) -> PortType {
        self.data.borrow().port.port_type
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

impl Debug for In {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "In {{ port: {:?} }}", self.data.borrow().port)
    }
}

impl Debug for Out {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Out {{ port: {:?} }}", self.data.borrow().port)
    }
}

#[derive(Clone)]
struct StlIn(In);

#[derive(Clone)]
struct StlOut(Out);

struct ArgData {
    
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
        let input = In::with_origin(port, origin);
        self.ins.push(input.clone());
        input
    }

    fn add_output(&mut self, port_type: PortType) -> Out {
        let port = Port {
            port_type,
            label: format!("o{}", self.outs.len()),
        };
        let output = Out::new(port);
        self.outs.push(output.clone());
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

        assert_eq!(0, n0.ins.len());
        assert_eq!(1, n0.outs.len());

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortType::Value, o0.clone());
        let i1 = n1.add_input(PortType::Value, o0.clone());

        assert_eq!(2, n1.ins.len());
        assert_eq!(0, n1.outs.len());

        let mut users = o0.users();
        assert_eq!(Some(i0), users.next());
        assert_eq!(Some(i1), users.next());
        assert_eq!(None, users.next());
    }

    #[test]
    #[should_panic="incompatible port types"]
    fn create_nodes_with_wrong_port_type() {
        let mut n0 = Node::new();
        let o0 = n0.add_output(PortType::Value);

        let mut n1 = Node::new();
        let i0 = n1.add_input(PortType::State, o0.clone());
    }
}
