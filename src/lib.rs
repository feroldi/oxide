use std::marker::PhantomData;
use std::rc::Rc;

trait PortKind {}

#[derive(Debug)]
struct PortValue;

#[derive(Debug)]
struct PortState;

impl PortKind for PortValue {}
impl PortKind for PortState {}

#[derive(Debug)]
struct Input<T: PortKind> {
    origin: Rc<Node>,
    phantom: PhantomData<T>,
}

impl<T: PortKind> Input<T> {
    fn new(origin: Rc<Node>) -> Input<T> {
        Input {
            origin,
            phantom: PhantomData,
        }
    }
}

#[derive(Debug)]
enum Node {
    I32Const(i32),
    Add(Input<PortValue>, Input<PortValue>),
}

trait Eval {
    fn eval(&self) -> i32;
}

impl Eval for Node {
    fn eval(&self) -> i32 {
        match *self {
            Node::I32Const(value) => value,
            Node::Add(ref lhs, ref rhs) => lhs.origin.eval() + rhs.origin.eval(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::rc::Rc;
    use super::{Eval, Input, Node};

    #[test]
    fn eval_add_constants() {
        let n1 = Rc::new(Node::I32Const(1));
        let n2 = Rc::new(Node::I32Const(2));
        let n3 = Rc::new(Node::Add(Input::new(n1.clone()), Input::new(n2.clone())));
        let n4 = Rc::new(Node::Add(Input::new(n1.clone()), Input::new(n2.clone())));
        let n5 = Rc::new(Node::Add(Input::new(n3.clone()), Input::new(n4.clone())));

        assert_eq!(6, n5.eval());
    }
}
