use std::{
    cell::{Cell, Ref, RefCell},
    fmt, ptr,
};

#[derive(Clone, Copy, PartialEq, Debug)]
struct NodeId(usize);

#[derive(Clone, Copy, PartialEq, Debug)]
struct InId {
    node: NodeId,
    index: usize,
}

#[derive(Clone, Copy, Debug)]
struct OutId {
    node: NodeId,
    index: usize,
}

struct InData {
    origin: OutId,
    prev_user: Cell<Option<InId>>,
    next_user: Cell<Option<InId>>,
}

#[derive(Clone, Default, Debug)]
struct OutData {
    users: Cell<Option<UserList>>,
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct UserList {
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

impl SigS {
    fn ins_len(&self) -> usize {
        self.val_ins + self.st_ins
    }

    fn outs_len(&self) -> usize {
        self.val_outs + self.st_outs
    }
}

trait Sig {
    fn sig(&self) -> SigS;
}

impl<S: Sig> Sig for NodeData<S> {
    fn sig(&self) -> SigS {
        self.data.sig()
    }
}

struct NodeCtxt<S> {
    nodes: RefCell<Vec<NodeData<S>>>,
}

impl<S> NodeCtxt<S> {
    fn new() -> NodeCtxt<S> {
        NodeCtxt {
            nodes: RefCell::new(vec![]),
        }
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

impl<S: Sig> NodeCtxt<S> {
    fn mk_node_with(&self, data: S, origins: &[OutId]) -> NodeId {
        // Node creation works as follows:
        // 1. Create the InData sequence, connecting sinks as you go.
        // 2. Initialize the OutData sequence with empty users.
        // 3. Push the new node to the node context and return its id.
        assert!(data.sig().ins_len() == origins.len());

        // Input ports are first pushed into this vector, so the node creation comes
        // down to just a push to the nodes vector.
        let mut new_node_inputs = Vec::<InData>::with_capacity(data.sig().ins_len());
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
                    let new_out_users = UserList {
                        first: users.first,
                        last: in_id,
                    };
                    (prev_user, new_out_users)
                }
                None => (
                    None, // No previous user.
                    UserList {
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

        let sig = data.sig();

        self.nodes.borrow_mut().push(NodeData {
            ins: new_node_inputs,
            outs: vec![OutData::default(); data.sig().outs_len()],
            data,
        });

        assert_eq!(
            self.node_data(node_id).outs.len(),
            sig.val_outs + sig.st_outs
        );

        node_id
    }
}

struct Graph<S> {
    ncx: NodeCtxt<S>,
}

impl<S> PartialEq for Graph<S> {
    fn eq(&self, other: &Graph<S>) -> bool {
        ptr::eq(self, other)
    }
}

impl<S> Graph<S> {
    fn new(ncx: NodeCtxt<S>) -> Graph<S> {
        Graph { ncx }
    }

    fn mk_node(&self, data: S) -> Node<S>
    where
        S: Sig,
    {
        let node_id = self.ncx.mk_node_with(data, &[]);
        Node {
            graph: self,
            id: node_id,
        }
    }

    fn node_builder(&self, data: S) -> GraphNodeBuilder<S>
    where
        S: Sig,
    {
        GraphNodeBuilder::new(self, data)
    }

    fn node_ref(&self, node_id: NodeId) -> Node<S> {
        assert!(node_id.0 < self.ncx.nodes.borrow().len());
        Node {
            graph: self,
            id: node_id,
        }
    }

    fn in_ref(&self, in_id: InId) -> In<S> {
        assert!(in_id.index < self.ncx.node_data(in_id.node).ins.len());
        In {
            node: self.node_ref(in_id.node),
            port: in_id.index,
        }
    }

    fn out_ref(&self, out_id: OutId) -> Out<S> {
        assert!(out_id.index < self.ncx.node_data(out_id.node).outs.len());
        Out {
            node: self.node_ref(out_id.node),
            port: out_id.index,
        }
    }
}

struct GraphNodeBuilder<'g, S> {
    graph: &'g Graph<S>,
    node_metadata: S,
    val_origins: Vec<ValOut<'g, S>>,
    st_origins: Vec<StOut<'g, S>>,
}

impl<'g, S: Sig> GraphNodeBuilder<'g, S> {
    fn new(graph: &'g Graph<S>, node_metadata: S) -> GraphNodeBuilder<'g, S> {
        let sig = node_metadata.sig();
        GraphNodeBuilder {
            graph,
            node_metadata,
            val_origins: Vec::with_capacity(sig.val_ins),
            st_origins: Vec::with_capacity(sig.st_ins),
        }
    }

    fn with_val(mut self, val_out: ValOut<'g, S>) -> GraphNodeBuilder<S> {
        assert!(self.val_origins.len() < self.node_metadata.sig().val_ins);
        self.val_origins.push(val_out);
        self
    }

    fn with_state(mut self, st_out: StOut<'g, S>) -> GraphNodeBuilder<S> {
        assert!(self.st_origins.len() < self.node_metadata.sig().st_ins);
        self.st_origins.push(st_out);
        self
    }

    fn finish(self) -> Node<'g, S> {
        let sig = self.node_metadata.sig();
        assert_eq!(self.val_origins.len(), sig.val_ins);
        assert_eq!(self.st_origins.len(), sig.st_ins);

        let origins: Vec<OutId> = {
            let val_origins = self.val_origins.iter().map(|val_out| val_out.0.id());
            let st_origins = self.st_origins.iter().map(|st_out| st_out.0.id());
            val_origins.chain(st_origins).collect()
        };

        assert_eq!(origins.len(), sig.val_ins + sig.st_ins);

        let node_id = self.graph.ncx.mk_node_with(self.node_metadata, &origins);

        Node {
            graph: self.graph,
            id: node_id,
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
struct Node<'g, S> {
    graph: &'g Graph<S>,
    id: NodeId,
}

impl<'g, S: fmt::Debug> fmt::Debug for Node<'g, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.data().data)
    }
}

impl<'g, S> Node<'g, S> {
    fn data(&self) -> Ref<'g, NodeData<S>> {
        self.graph.ncx.node_data(self.id)
    }
}

impl<'g, S: Sig + Clone + Copy> Node<'g, S> {
    fn val_in(&self, port: usize) -> ValIn<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.val_ins);
        ValIn(In { node: *self, port })
    }

    fn val_out(&self, port: usize) -> ValOut<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.val_outs);
        ValOut(Out { node: *self, port })
    }

    fn st_in(&self, port: usize) -> StIn<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.st_ins);
        StIn(In {
            node: *self,
            port: sig.val_ins + port,
        })
    }

    fn st_out(&self, port: usize) -> StOut<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.st_outs);
        StOut(Out {
            node: *self,
            port: sig.val_outs + port,
        })
    }
}

#[derive(PartialEq, Debug)]
struct In<'g, S> {
    node: Node<'g, S>,
    port: usize,
}

impl<'g, S> In<'g, S> {
    fn id(&self) -> InId {
        InId {
            node: self.node.id,
            index: self.port,
        }
    }

    fn data(&self) -> Ref<'g, InData> {
        self.node.graph.ncx.in_data(self.id())
    }

    fn origin(&self) -> Out<'g, S> {
        let origin = self.data().origin;
        self.node.graph.out_ref(origin)
    }
}

#[derive(PartialEq, Debug)]
struct Out<'g, S> {
    node: Node<'g, S>,
    port: usize,
}

impl<'g, S> Out<'g, S> {
    fn id(&self) -> OutId {
        OutId {
            node: self.node.id,
            index: self.port,
        }
    }

    fn data(&self) -> Ref<'g, OutData> {
        self.node.graph.ncx.out_data(self.id())
    }

    fn users(&self) -> Users<'g, S> {
        let in_ref = |in_id| self.node.graph.in_ref(in_id);
        Users {
            first_and_last: self
                .data()
                .users
                .get()
                .map(|users| (in_ref(users.first), in_ref(users.last))),
        }
    }
}

struct Users<'g, S> {
    first_and_last: Option<(In<'g, S>, In<'g, S>)>,
}

impl<'g, S> Iterator for Users<'g, S> {
    type Item = In<'g, S>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.first_and_last.take() {
            Some((first, last)) => {
                if first.id() != last.id() {
                    if let Some(next_user) = first.data().next_user.get() {
                        self.first_and_last = Some((first.node.graph.in_ref(next_user), last));
                    }
                }
                Some(first)
            }
            None => None,
        }
    }
}

#[derive(PartialEq, Debug)]
struct ValIn<'g, S>(In<'g, S>);

impl<'g, S> ValIn<'g, S> {
    fn origin(&self) -> ValOut<'g, S> {
        ValOut(self.0.origin())
    }
}

#[derive(PartialEq, Debug)]
struct StIn<'g, S>(In<'g, S>);

impl<'g, S> StIn<'g, S> {
    fn origin(&self) -> StOut<'g, S> {
        StOut(self.0.origin())
    }
}

#[derive(PartialEq, Debug)]
struct ValOut<'g, S>(Out<'g, S>);

impl<'g, S> ValOut<'g, S> {
    fn users(&self) -> impl Iterator<Item = ValIn<'g, S>> {
        self.0.users().map(ValIn)
    }
}

#[derive(PartialEq, Debug)]
struct StOut<'g, S>(Out<'g, S>);

impl<'g, S> StOut<'g, S> {
    fn users(&self) -> impl Iterator<Item = StIn<'g, S>> {
        self.0.users().map(StIn)
    }
}

#[cfg(test)]
mod test {
    use super::{Graph, NodeCtxt, OutId, Sig, SigS};

    #[derive(Clone, Copy, PartialEq, Debug)]
    enum TestData {
        Lit(u32),
        Neg,
        St,
        BinAdd,
        LoadOffset,
    }

    impl Sig for TestData {
        fn sig(&self) -> SigS {
            match self {
                TestData::Lit(..) => SigS {
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::Neg => SigS {
                    val_ins: 1,
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::St => SigS {
                    st_outs: 1,
                    ..SigS::default()
                },
                TestData::BinAdd => SigS {
                    val_ins: 2,
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::LoadOffset => SigS {
                    val_ins: 2,
                    val_outs: 1,
                    st_ins: 1,
                    st_outs: 1,
                },
            }
        }
    }

    #[test]
    fn create_single_node() {
        let ncx = NodeCtxt::new();
        let n0 = ncx.mk_node_with(TestData::Lit(0), &[]);
        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());
    }

    #[test]
    fn create_node_with_an_input() {
        let ncx = NodeCtxt::new();
        let n0 = ncx.mk_node_with(TestData::Lit(0), &[]);
        let n1 = ncx.mk_node_with(TestData::Neg, &[OutId { node: n0, index: 0 }]);

        assert_eq!(n0, ncx.node_data(n1).ins[0].origin.node);
    }

    #[test]
    fn create_node_with_an_input_using_builder() {
        let ncx = NodeCtxt::new();
        let g = Graph::new(ncx);

        let n0 = g.mk_node(TestData::Lit(0));
        let n1 = g
            .node_builder(TestData::Neg)
            .with_val(n0.val_out(0))
            .finish();

        assert_eq!(n0.id, n1.data().ins[0].origin.node);
        assert_eq!(n0.val_out(0), n1.val_in(0).origin());
    }

    #[test]
    fn create_node_with_input_ports() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node_with(TestData::Lit(2), &[]);

        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());

        let n1 = ncx.mk_node_with(TestData::Lit(3), &[]);

        assert_eq!(0, ncx.node_data(n1).ins.len());
        assert_eq!(1, ncx.node_data(n1).outs.len());

        let n2 = ncx.mk_node_with(
            TestData::BinAdd,
            &[OutId { node: n0, index: 0 }, OutId { node: n1, index: 0 }],
        );

        assert_eq!(2, ncx.node_data(n2).ins.len());
        assert_eq!(1, ncx.node_data(n2).outs.len());

        assert_eq!(
            n2,
            ncx.node_data(n0).outs[0].users.get().unwrap().first.node
        );
        assert_eq!(n2, ncx.node_data(n0).outs[0].users.get().unwrap().last.node);
        assert_eq!(
            n2,
            ncx.node_data(n1).outs[0].users.get().unwrap().first.node
        );
        assert_eq!(n2, ncx.node_data(n1).outs[0].users.get().unwrap().last.node);
    }

    #[test]
    fn create_node_with_values_and_states_using_builder() {
        let ncx = NodeCtxt::new();
        let g = Graph::new(ncx);

        let n0 = g.mk_node(TestData::Lit(2));
        let n1 = g.mk_node(TestData::Lit(3));
        let n2 = g.mk_node(TestData::St);

        let n3 = g
            .node_builder(TestData::LoadOffset)
            .with_val(n0.val_out(0))
            .with_val(n1.val_out(0))
            .with_state(n2.st_out(0))
            .finish();

        assert_eq!(n0.val_out(0), n3.val_in(0).origin());
        assert_eq!(n1.val_out(0), n3.val_in(1).origin());
        assert_eq!(n2.st_out(0), n3.st_in(0).origin());
    }
}
