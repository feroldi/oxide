use std::cell::{Cell, Ref, RefCell};

#[derive(Clone, Copy, PartialEq)]
struct NodeId(usize);

#[derive(Clone, Copy)]
struct InId {
    node: NodeId,
    index: usize,
}

#[derive(Clone, Copy)]
struct OutId {
    node: NodeId,
    index: usize,
}

struct InData {
    origin: OutId,
    prev_user: Cell<Option<InId>>,
    next_user: Cell<Option<InId>>,
}

#[derive(Clone, Default)]
struct OutData {
    users: Cell<Option<Users>>,
}

#[derive(Clone, Copy)]
struct Users {
    first: InId,
    last: InId,
}

struct NodeData<S> {
    ins: Vec<InData>,
    outs: Vec<OutData>,
    data: S,
}

#[derive(Debug, Copy, Clone, PartialEq, Default)]
struct SigS {
    val_ins: usize,
    val_outs: usize,
    st_ins: usize,
    st_outs: usize,
}

trait Sig {
    fn sig(&self) -> SigS;

    fn ins_len(&self) -> usize {
        self.sig().val_ins + self.sig().st_ins
    }

    fn outs_len(&self) -> usize {
        self.sig().val_outs + self.sig().st_outs
    }
}

struct NodeCtxt<S> {
    nodes: RefCell<Vec<NodeData<S>>>,
}

impl<S: Sig> NodeCtxt<S> {
    fn new() -> NodeCtxt<S> {
        NodeCtxt {
            nodes: RefCell::new(vec![]),
        }
    }

    fn mk_node(&self, data: S, origins: &[OutId]) -> NodeId {
        // TODO:
        // + Create the InData sequence, connecting sinks as you go.
        // + Initialize the OutData sequence with empty users.
        // + Push the new node to the node context and return its id.
        assert!(data.ins_len() == origins.len());

        let mut new_node_inputs = Vec::<InData>::with_capacity(data.ins_len());
        let node_id = NodeId(self.nodes.borrow().len());

        for (i, &origin) in origins.iter().enumerate() {
            let in_id = InId {
                node: node_id,
                index: i,
            };
            let (prev_user, new_out_users) = match self.out_data(origin).users.get() {
                Some(users) => {
                    if users.last.node == node_id {
                        // FIXME: Is this a dead branch?
                        new_node_inputs[users.last.index].next_user.set(Some(in_id));
                    } else {
                        self.in_data(users.last).next_user.set(Some(in_id));
                    }
                    let prev_user = Some(users.last);
                    let new_out_users = Users {
                        first: users.first,
                        last: in_id,
                    };
                    (prev_user, new_out_users)
                }
                None => (
                    None,
                    Users {
                        first: in_id,
                        last: in_id,
                    },
                ),
            };
            self.out_data(origin).users.set(Some(new_out_users));
            new_node_inputs.push(InData {
                origin,
                prev_user: Cell::new(prev_user),
                next_user: Cell::default(),
            });
        }

        self.nodes.borrow_mut().push(NodeData {
            ins: new_node_inputs,
            outs: vec![OutData::default(); data.outs_len()],
            data,
        });

        node_id
    }

    fn node_data(&self, id: NodeId) -> Ref<NodeData<S>> {
        Ref::map(self.nodes.borrow(), |nodes| &nodes[id.0])
    }

    fn in_data(&self, id: InId) -> Ref<InData> {
        Ref::map(self.node_data(id.node), |data| &data.ins[id.index])
    }

    fn out_data(&self, id: OutId) -> Ref<OutData> {
        Ref::map(self.node_data(id.node), |data| &data.outs[id.index])
    }
}

#[cfg(test)]
mod test {
    use super::{NodeCtxt, OutId, Sig, SigS};

    enum TestData {
        Lit(u32),
        Add,
    }

    impl Sig for TestData {
        fn sig(&self) -> SigS {
            match self {
                TestData::Lit(..) => SigS {
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::Add => SigS {
                    val_ins: 2,
                    val_outs: 1,
                    ..SigS::default()
                },
            }
        }
    }

    #[test]
    fn create_nodes() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(2), &[]);

        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());

        let n1 = ncx.mk_node(TestData::Lit(3), &[]);

        assert_eq!(0, ncx.node_data(n1).ins.len());
        assert_eq!(1, ncx.node_data(n1).outs.len());

        let n2 = ncx.mk_node(
            TestData::Add,
            &[OutId { node: n0, index: 0 }, OutId { node: n1, index: 0 }],
        );

        assert_eq!(2, ncx.node_data(n2).ins.len());
        assert_eq!(1, ncx.node_data(n2).outs.len());
    }
}
