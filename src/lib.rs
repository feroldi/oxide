#![feature(hash_raw_entry)]

use std::{
    cell::{Cell, Ref, RefCell},
    collections::{hash_map::RawEntryMut, HashMap},
    fmt,
    hash::{BuildHasher, Hash, Hasher},
    ptr,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct NodeId(usize);

#[derive(Clone, Copy, PartialEq, Debug)]
struct InId {
    node: NodeId,
    index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum NodeKind<S> {
    Op(S),
    Apply {
        arg_val_ins: usize,
        arg_st_ins: usize,
        region_val_res: usize,
        region_st_res: usize,
    },
    Gamma {
        val_ins: usize,
        val_outs: usize,
        st_ins: usize,
        st_outs: usize,
    },
}

struct NodeData<S> {
    ins: Vec<InData>,
    outs: Vec<OutData>,
    inner_regions: Option<InnerRegionList>,
    outer_region: RegionId,
    kind: NodeKind<S>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct RegionId(usize);

struct InnerRegionList {
    first_region: RegionId,
    last_region: RegionId,
}

struct ArgData {
    input: InId,
    users: Cell<Option<UserList>>,
}

struct ResData {
    result_from: OutId,
    mapped_to: OutId,
}

struct RegionData {
    args: Vec<ArgData>,
    res: Vec<ResData>,
    prev_region: Cell<Option<RegionId>>,
    next_region: Cell<Option<RegionId>>,
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
        self.kind.sig()
    }
}

impl<S: Sig> Sig for NodeKind<S> {
    fn sig(&self) -> SigS {
        match self {
            NodeKind::Op(s) => s.sig(),
            &NodeKind::Apply {
                arg_val_ins,
                arg_st_ins,
                region_val_res,
                region_st_res,
            } => SigS {
                val_ins: 1 + arg_val_ins, // function input + argument inputs
                st_ins: arg_st_ins,
                val_outs: region_val_res,
                st_outs: region_st_res,
            },
            &NodeKind::Gamma {
                val_ins,
                val_outs,
                st_ins,
                st_outs,
            } => {
                SigS {
                    val_ins: 1 + val_ins, // predicate + inputs
                    val_outs,
                    st_ins,
                    st_outs,
                }
            }
        }
    }
}

struct NodeTerm<S> {
    kind: NodeKind<S>,
    origins: Vec<OutId>,
}

impl<S: PartialEq> PartialEq for NodeTerm<S> {
    fn eq(&self, other: &NodeTerm<S>) -> bool {
        self.kind == other.kind && self.origins == other.origins
    }
}

impl<S: Eq> Eq for NodeTerm<S> {}

impl<S: Hash> Hash for NodeTerm<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
        self.origins.hash(state);
    }
}

struct NodeCtxt<S> {
    nodes: RefCell<Vec<NodeData<S>>>,
    interned_nodes: RefCell<HashMap<NodeTerm<S>, NodeId>>,
}

impl<S> NodeCtxt<S> {
    fn new() -> NodeCtxt<S>
    where
        S: Eq + Hash,
    {
        NodeCtxt {
            nodes: RefCell::new(vec![]),
            interned_nodes: RefCell::default(),
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

    fn hash_node_terms(&self, kind: &NodeKind<S>, origins: &[OutId]) -> u64
    where
        S: Eq + Hash,
    {
        let mut hasher = self.interned_nodes.borrow().hasher().build_hasher();
        kind.hash(&mut hasher);
        origins.hash(&mut hasher);
        hasher.finish()
    }

    fn mk_node_with(&self, kind: NodeKind<S>, origins: &[OutId]) -> NodeId
    where
        S: Sig + Eq + Hash + Clone,
    {
        assert_eq!(kind.sig().ins_len(), origins.len());

        let create_node = |kind: NodeKind<S>, origins: &[OutId]| {
            // Node creation works as follows:
            // 1. Create the InData sequence, operanding sinks as you go.
            // 2. Initialize the OutData sequence with empty users.
            // 3. Push the new node to the node context and return its id.

            // Input ports are put into this vector so the node creation comes down to just
            // a push into the `self.nodes`.
            let mut new_node_inputs = Vec::<InData>::with_capacity(kind.sig().ins_len());
            let node_id = NodeId(self.nodes.borrow().len());

            for (i, &origin) in origins.iter().enumerate() {
                let new_in_id = InId {
                    node: node_id,
                    index: i,
                };
                let (prev_user, new_user_list) = match self.out_data(origin).users.get() {
                    Some(UserList { first, last }) => {
                        if last.node == node_id {
                            new_node_inputs[last.index].next_user.set(Some(new_in_id));
                        } else {
                            self.in_data(last).next_user.set(Some(new_in_id));
                        }
                        let new_user_list = UserList {
                            first,
                            last: new_in_id,
                        };
                        (Some(last), new_user_list)
                    }
                    None => (
                        None, // No previous user.
                        UserList {
                            first: new_in_id,
                            last: new_in_id,
                        },
                    ),
                };
                self.out_data(origin).users.set(Some(new_user_list));
                new_node_inputs.push(InData {
                    origin,
                    prev_user: Cell::new(prev_user),
                    next_user: Cell::default(),
                });
            }

            let sig = kind.sig();

            self.nodes.borrow_mut().push(NodeData {
                ins: new_node_inputs,
                outs: vec![OutData::default(); kind.sig().outs_len()],
                inner_regions: None,
                // FIXME replace with an argument from mk_node_with.
                outer_region: RegionId(0),
                kind,
            });

            assert_eq!(self.node_data(node_id).ins.len(), sig.ins_len());
            assert_eq!(self.node_data(node_id).outs.len(), sig.outs_len());

            node_id
        };

        let node_term = NodeTerm {
            kind: kind.clone(),
            origins: origins.into(),
        };

        let node_hash = self.hash_node_terms(&kind, origins);
        let mut interned_nodes = self.interned_nodes.borrow_mut();
        let entry = interned_nodes
            .raw_entry_mut()
            .from_key_hashed_nocheck(node_hash, &node_term);

        match entry {
            RawEntryMut::Occupied(e) => *e.get(),
            RawEntryMut::Vacant(e) => {
                let node_id = create_node(kind, origins);
                e.insert_hashed_nocheck(node_hash, node_term, node_id);
                node_id
            }
        }
    }

    fn mk_node(&self, op: S) -> Node<S>
    where
        S: Sig + Eq + Hash + Clone,
    {
        let node_id = self.mk_node_with(NodeKind::Op(op), &[]);
        Node {
            ctxt: self,
            id: node_id,
        }
    }

    fn node_builder(&self, op: S) -> NodeBuilder<S>
    where
        S: Sig,
    {
        NodeBuilder::new(self, NodeKind::Op(op))
    }

    fn node_ref(&self, node_id: NodeId) -> Node<S> {
        assert!(node_id.0 < self.nodes.borrow().len());
        Node {
            ctxt: self,
            id: node_id,
        }
    }

    fn in_ref(&self, in_id: InId) -> In<S> {
        assert!(in_id.index < self.node_data(in_id.node).ins.len());
        In {
            node: self.node_ref(in_id.node),
            port: in_id.index,
        }
    }

    fn out_ref(&self, out_id: OutId) -> Out<S> {
        assert!(out_id.index < self.node_data(out_id.node).outs.len());
        Out {
            node: self.node_ref(out_id.node),
            port: out_id.index,
        }
    }
}

impl<S> PartialEq for NodeCtxt<S> {
    fn eq(&self, other: &NodeCtxt<S>) -> bool {
        ptr::eq(self, other)
    }
}

struct NodeBuilder<'g, S> {
    ctxt: &'g NodeCtxt<S>,
    node_kind: NodeKind<S>,
    val_origins: Vec<ValOut<'g, S>>,
    st_origins: Vec<StOut<'g, S>>,
}

impl<'g, S: Sig> NodeBuilder<'g, S> {
    fn new(ctxt: &'g NodeCtxt<S>, node_kind: NodeKind<S>) -> NodeBuilder<'g, S> {
        let sig = node_kind.sig();
        NodeBuilder {
            ctxt,
            node_kind,
            val_origins: Vec::with_capacity(sig.val_ins),
            st_origins: Vec::with_capacity(sig.st_ins),
        }
    }

    fn operand(mut self, val_out: ValOut<'g, S>) -> NodeBuilder<'g, S> {
        assert!(self.val_origins.len() < self.node_kind.sig().val_ins);
        self.val_origins.push(val_out);
        self
    }

    fn operands(mut self, val_outs: &[ValOut<'g, S>]) -> NodeBuilder<'g, S>
    where
        S: Clone,
    {
        assert!(self.val_origins.is_empty());
        assert_eq!(self.node_kind.sig().val_ins, val_outs.len());
        self.val_origins.extend(val_outs.iter().cloned());
        self
    }

    fn state(mut self, st_out: StOut<'g, S>) -> NodeBuilder<'g, S> {
        assert!(self.st_origins.len() < self.node_kind.sig().st_ins);
        self.st_origins.push(st_out);
        self
    }

    fn states(mut self, st_outs: &[StOut<'g, S>]) -> NodeBuilder<'g, S>
    where
        S: Clone,
    {
        assert!(self.st_origins.is_empty());
        assert_eq!(self.node_kind.sig().st_ins, st_outs.len());
        self.st_origins.extend(st_outs.iter().cloned());
        self
    }

    fn finish(self) -> Node<'g, S>
    where
        S: Eq + Hash + Clone,
    {
        let sig = self.node_kind.sig();
        assert_eq!(self.val_origins.len(), sig.val_ins);
        assert_eq!(self.st_origins.len(), sig.st_ins);

        let origins: Vec<OutId> = {
            let val_origins = self.val_origins.iter().map(|val_out| val_out.0.id());
            let st_origins = self.st_origins.iter().map(|st_out| st_out.0.id());
            val_origins.chain(st_origins).collect()
        };

        assert_eq!(origins.len(), sig.val_ins + sig.st_ins);

        let node_id = self.ctxt.mk_node_with(self.node_kind, &origins);

        Node {
            ctxt: self.ctxt,
            id: node_id,
        }
    }
}

#[derive(Clone, Copy, PartialEq)]
struct Node<'g, S> {
    ctxt: &'g NodeCtxt<S>,
    id: NodeId,
}

impl<'g, S: fmt::Debug> fmt::Debug for Node<'g, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.data().kind)
    }
}

impl<'g, S> Node<'g, S> {
    fn data(&self) -> Ref<'g, NodeData<S>> {
        self.ctxt.node_data(self.id)
    }
}

impl<'g, S: Sig + Copy> Node<'g, S> {
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

#[derive(Copy, Clone, PartialEq, Debug)]
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
        self.node.ctxt.in_data(self.id())
    }

    fn origin(&self) -> Out<'g, S> {
        let origin = self.data().origin;
        self.node.ctxt.out_ref(origin)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
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
        self.node.ctxt.out_data(self.id())
    }

    fn users(&self) -> Users<'g, S> {
        let in_ref = |in_id| self.node.ctxt.in_ref(in_id);
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
                        self.first_and_last = Some((first.node.ctxt.in_ref(next_user), last));
                    }
                }
                Some(first)
            }
            None => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct ValIn<'g, S>(In<'g, S>);

impl<'g, S> ValIn<'g, S> {
    fn origin(&self) -> ValOut<'g, S> {
        ValOut(self.0.origin())
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct StIn<'g, S>(In<'g, S>);

impl<'g, S> StIn<'g, S> {
    fn origin(&self) -> StOut<'g, S> {
        StOut(self.0.origin())
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct ValOut<'g, S>(Out<'g, S>);

impl<'g, S> ValOut<'g, S> {
    fn users(&self) -> impl Iterator<Item = ValIn<'g, S>> {
        self.0.users().map(ValIn)
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
struct StOut<'g, S>(Out<'g, S>);

impl<'g, S> StOut<'g, S> {
    fn users(&self) -> impl Iterator<Item = StIn<'g, S>> {
        self.0.users().map(StIn)
    }
}

#[cfg(test)]
mod test {
    use super::{NodeCtxt, NodeKind, OutId, Sig, SigS};

    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum TestData {
        Lit(u32),
        Neg,
        St,
        BinAdd,
        LoadOffset,
        OpA,
        OpB,
        OpC,
    }

    impl Sig for TestData {
        fn sig(&self) -> SigS {
            match self {
                TestData::Lit(..) => SigS {
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::Neg | TestData::OpA | TestData::OpB | TestData::OpC => SigS {
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
        let n0 = ncx.mk_node_with(NodeKind::Op(TestData::Lit(0)), &[]);
        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());
    }

    #[test]
    fn create_node_with_an_input() {
        let ncx = NodeCtxt::new();
        let n0 = ncx.mk_node_with(NodeKind::Op(TestData::Lit(0)), &[]);
        let n1 = ncx.mk_node_with(NodeKind::Op(TestData::Neg), &[OutId { node: n0, index: 0 }]);

        assert_eq!(n0, ncx.node_data(n1).ins[0].origin.node);
    }

    #[test]
    fn create_node_with_an_input_using_builder() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(0));
        let n1 = ncx
            .node_builder(TestData::Neg)
            .operand(n0.val_out(0))
            .finish();

        assert_eq!(n0.id, n1.data().ins[0].origin.node);
        assert_eq!(n0.val_out(0), n1.val_in(0).origin());
    }

    #[test]
    fn create_node_with_input_ports() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node_with(NodeKind::Op(TestData::Lit(2)), &[]);

        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());

        let n1 = ncx.mk_node_with(NodeKind::Op(TestData::Lit(3)), &[]);

        assert_eq!(0, ncx.node_data(n1).ins.len());
        assert_eq!(1, ncx.node_data(n1).outs.len());

        let n2 = ncx.mk_node_with(
            NodeKind::Op(TestData::BinAdd),
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
    fn create_node_operands_and_states_using_builder_single() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(2));
        let n1 = ncx.mk_node(TestData::Lit(3));
        let n2 = ncx.mk_node(TestData::St);

        let n3 = ncx
            .node_builder(TestData::LoadOffset)
            .operand(n0.val_out(0))
            .operand(n1.val_out(0))
            .state(n2.st_out(0))
            .finish();

        assert_eq!(n0.val_out(0), n3.val_in(0).origin());
        assert_eq!(n1.val_out(0), n3.val_in(1).origin());
        assert_eq!(n2.st_out(0), n3.st_in(0).origin());
    }

    #[test]
    fn create_node_operands_and_states_using_builder_slice() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(2));
        let n1 = ncx.mk_node(TestData::Lit(3));
        let n2 = ncx.mk_node(TestData::St);

        let n3 = ncx
            .node_builder(TestData::LoadOffset)
            .operands(&[n0.val_out(0), n1.val_out(0)])
            .states(&[n2.st_out(0)])
            .finish();

        assert_eq!(n0.val_out(0), n3.val_in(0).origin());
        assert_eq!(n1.val_out(0), n3.val_in(1).origin());
        assert_eq!(n2.st_out(0), n3.st_in(0).origin());
    }

    #[test]
    fn users_iterator() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(0));

        let n1 = ncx
            .node_builder(TestData::OpA)
            .operand(n0.val_out(0))
            .finish();

        let n2 = ncx
            .node_builder(TestData::OpB)
            .operand(n0.val_out(0))
            .finish();

        let n3 = ncx
            .node_builder(TestData::OpC)
            .operand(n0.val_out(0))
            .finish();

        let mut users = n0.val_out(0).users();

        assert_eq!(Some(n1.val_in(0)), users.next());
        assert_eq!(Some(n2.val_in(0)), users.next());
        assert_eq!(Some(n3.val_in(0)), users.next());
        assert_eq!(None, users.next());
    }

    #[test]
    fn reuse_existing_eq_nodes_at_creation() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(2));
        let n1 = ncx.mk_node(TestData::Lit(3));
        let n2 = ncx.mk_node(TestData::Lit(2));

        assert_eq!(n0.id, n2.id);
        assert_ne!(n0.id, n1.id);
        assert_ne!(n1.id, n2.id);

        let n3 = ncx
            .node_builder(TestData::BinAdd)
            .operand(n0.val_out(0))
            .operand(n1.val_out(0))
            .finish();

        let n4 = ncx
            .node_builder(TestData::BinAdd)
            .operand(n0.val_out(0))
            .operand(n2.val_out(0))
            .finish();

        let n5 = ncx
            .node_builder(TestData::BinAdd)
            .operand(n2.val_out(0))
            .operand(n1.val_out(0))
            .finish();

        assert_ne!(n3.id, n4.id);
        assert_ne!(n4.id, n5.id);
        assert_eq!(n3.id, n5.id);
    }
}
