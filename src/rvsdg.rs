use smallvec::SmallVec;
use std::{
    cell::{Cell, Ref, RefCell},
    fmt::{self, Debug},
    hash::Hash,
    io::{self, Write},
    ptr,
};

/// An index for a NodeData in a NodeCtxt.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct NodeId(usize);

/// An index for a RegionData in a NodeCtxt.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct RegionId(usize);

/// An index for a UserData of an input or result port.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum UserId {
    In { node: NodeId, index: usize },
    Res { region: RegionId, index: usize },
}

impl UserId {
    pub fn node_id(&self) -> Option<NodeId> {
        match self {
            &UserId::In { node, .. } => Some(node),
            _ => None,
        }
    }
}

/// An index for an OriginData of an output or argument port.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum OriginId {
    Out { node: NodeId, index: usize },
    Arg { region: RegionId, index: usize },
}

impl OriginId {
    pub fn node_id(&self) -> Option<NodeId> {
        match self {
            &OriginId::Out { node, .. } => Some(node),
            _ => None,
        }
    }
}

/// A UserData contains information about an input or result port.
#[derive(Clone, Default, Debug)]
pub struct UserData {
    origin: Cell<Option<OriginId>>,
    sinks: SmallVec<[OriginId; 2]>,
    prev_user: Cell<Option<UserId>>,
    next_user: Cell<Option<UserId>>,
}

/// An OriginData contains information about an output or argument port.
#[derive(Clone, Default, Debug)]
pub struct OriginData {
    sources: SmallVec<[UserId; 2]>,
    users: Cell<Option<UserIdList>>,
}

/// A linked list of users connected to a common origin.
#[derive(Clone, Copy, PartialEq, Debug)]
pub struct UserIdList {
    first: UserId,
    last: UserId,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum NodeKind<S> {
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
    Omega {
        imports: usize,
        exports: usize,
    },
}

pub struct NodeData<S> {
    ins: Vec<UserData>,
    outs: Vec<OriginData>,
    inner_regions: Cell<Option<InnerRegionList>>,
    kind: NodeKind<S>,
}

#[derive(Copy, Clone)]
pub struct InnerRegionList {
    first_region: RegionId,
    last_region: RegionId,
}

pub struct RegionData {
    res: Vec<UserData>,
    args: Vec<OriginData>,
    prev_region: Cell<Option<RegionId>>,
    next_region: Cell<Option<RegionId>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct SigS {
    pub val_ins: usize,
    pub val_outs: usize,
    pub st_ins: usize,
    pub st_outs: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Default)]
pub struct RegionSigS {
    pub val_args: usize,
    pub val_res: usize,
    pub st_args: usize,
    pub st_res: usize,
}

impl SigS {
    pub fn num_input_ports(&self) -> usize {
        self.val_ins + self.st_ins
    }

    pub fn num_output_ports(&self) -> usize {
        self.val_outs + self.st_outs
    }
}

impl RegionSigS {
    pub fn num_argument_ports(&self) -> usize {
        self.val_args + self.st_args
    }

    pub fn num_result_ports(&self) -> usize {
        self.val_res + self.st_res
    }
}

pub trait Sig {
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
                ..SigS::default()
            },
            &NodeKind::Gamma {
                val_ins,
                val_outs,
                st_ins,
                st_outs,
            } => SigS {
                val_ins: 1 + val_ins, // predicate + inputs
                val_outs,
                st_ins,
                st_outs,
                ..SigS::default()
            },
            &NodeKind::Omega { .. } => SigS::default(),
        }
    }
}

pub struct NodeCtxt<S> {
    nodes: RefCell<Vec<NodeData<S>>>,
    regions: RefCell<Vec<RegionData>>,
}

impl<S> NodeCtxt<S> {
    pub fn new() -> NodeCtxt<S>
    where
        S: Eq + Hash,
    {
        NodeCtxt {
            nodes: RefCell::new(vec![]),
            regions: RefCell::new(vec![]),
        }
    }

    // FIXME: This doesn't do interning. How could we do it?
    fn create_node(&self, node_kind: NodeKind<S>) -> NodeId
    where
        S: Sig,
    {
        let mut nodes = self.nodes.borrow_mut();
        let node_id = NodeId(nodes.len());
        nodes.push(NodeData {
            ins: vec![UserData::default(); node_kind.sig().num_input_ports()],
            outs: vec![OriginData::default(); node_kind.sig().num_output_ports()],
            inner_regions: Cell::default(),
            kind: node_kind,
        });
        node_id
    }

    fn connect_ports(&self, user_id: UserId, origin_id: OriginId) {
        let user_data = self.user_data(user_id);

        assert_eq!(user_data.origin.get(), None);
        assert_eq!(user_data.prev_user.get(), None);
        assert_eq!(user_data.next_user.get(), None);

        user_data.origin.set(Some(origin_id));

        let origin_data = self.origin_data(origin_id);

        let new_user_list = match origin_data.users.get() {
            Some(UserIdList { first, last }) => {
                self.user_data(last).next_user.set(Some(user_id));
                user_data.prev_user.set(Some(last));
                UserIdList {
                    first,
                    last: user_id,
                }
            }
            None => UserIdList {
                first: user_id,
                last: user_id,
            },
        };

        origin_data.users.set(Some(new_user_list));
    }

    pub fn node_data(&self, id: NodeId) -> Ref<NodeData<S>> {
        Ref::map(self.nodes.borrow(), |nodes| &nodes[id.0])
    }

    pub fn region_data(&self, id: RegionId) -> Ref<RegionData> {
        Ref::map(self.regions.borrow(), |regions| &regions[id.0])
    }

    pub fn user_data(&self, user_id: UserId) -> Ref<UserData> {
        match user_id {
            UserId::In { node, index } => {
                Ref::map(self.node_data(node), |node_data| &node_data.ins[index])
            }
            UserId::Res { region, index } => Ref::map(self.region_data(region), |region_data| {
                &region_data.res[index]
            }),
        }
    }

    pub fn origin_data(&self, origin_id: OriginId) -> Ref<OriginData> {
        match origin_id {
            OriginId::Out { node, index } => {
                Ref::map(self.node_data(node), |node_data| &node_data.outs[index])
            }
            OriginId::Arg { region, index } => Ref::map(self.region_data(region), |region_data| {
                &region_data.args[index]
            }),
        }
    }

    pub fn mk_node(&self, op: S) -> Node<S>
    where
        S: Sig + Eq + Hash + Clone,
    {
        let node_id = self.create_node(NodeKind::Op(op));
        Node {
            ctxt: self,
            id: node_id,
        }
    }

    pub fn node_ref(&self, node_id: NodeId) -> Node<S> {
        assert!(node_id.0 < self.nodes.borrow().len());
        Node {
            ctxt: self,
            id: node_id,
        }
    }

    pub fn user_ref<'g>(&'g self, user_id: UserId) -> User<'g, S> {
        match user_id {
            UserId::In { node, index } => assert!(index < self.node_data(node).ins.len()),
            UserId::Res { region, index } => assert!(index < self.region_data(region).res.len()),
        }

        User {
            ctxt: self,
            user_id,
        }
    }

    pub fn origin_ref<'g>(&'g self, origin_id: OriginId) -> Origin<'g, S> {
        match origin_id {
            OriginId::Out { node, index } => assert!(index < self.node_data(node).outs.len()),
            OriginId::Arg { region, index } => assert!(index < self.region_data(region).args.len()),
        }

        Origin {
            ctxt: self,
            origin_id,
        }
    }

    pub fn print(&self, out: &mut dyn Write) -> io::Result<()>
    where
        S: Sig + Debug + Copy,
    {
        writeln!(out, "digraph rvsdg {{")?;
        writeln!(out, "    node [shape=record]")?;
        writeln!(out, "    edge [arrowhead=none]")?;
        for idx in 0..self.nodes.borrow().len() {
            let node = self.node_ref(NodeId(idx));
            let sig = node.kind().sig();

            match *node.kind() {
                NodeKind::Op(ref operation) => {
                    let dot_ins = (0..sig.num_input_ports())
                        .map(|i| format!("<i{0}>{0}", i))
                        .collect::<Vec<_>>()
                        .join("|");
                    let dot_outs = (0..sig.num_output_ports())
                        .map(|i| format!("<o{0}>{0}", i))
                        .collect::<Vec<_>>()
                        .join("|");
                    let mut label_op = String::with_capacity(16);
                    for c in format!("{:?}", operation).chars() {
                        if c == '{' || c == '}' {
                            label_op.push('\\');
                        }
                        label_op.push(c);
                    }
                    let label_value = vec![dot_ins, label_op, dot_outs]
                        .into_iter()
                        .filter(|s| !s.is_empty())
                        .collect::<Vec<_>>()
                        .join("}|{");
                    let label = format!("{{{{{}}}}}", label_value);
                    writeln!(out, r#"    n{} [label="{}"]"#, node.id.0, label)?;
                }
                _ => unimplemented!(),
            }

            for i in 0..sig.val_ins {
                let origin = node.val_in(i).origin();
                match origin.0.origin_id {
                    OriginId::Out {
                        node: origin_node_id,
                        index,
                    } => {
                        let port_origin = index;
                        let port_user = i;
                        writeln!(
                            out,
                            "    n{}:o{} -> n{}:i{} [color=blue]",
                            origin_node_id.0, port_origin, node.id.0, port_user
                        )?;
                    }
                    _ => unimplemented!(),
                }
            }

            for i in 0..sig.st_ins {
                let origin = node.st_in(i).origin();
                match origin.0.origin_id {
                    OriginId::Out {
                        node: origin_node_id,
                        index,
                    } => {
                        let port_origin = index;
                        let port_user = sig.val_ins + i;
                        writeln!(
                            out,
                            "    n{}:o{} -> n{}:i{} [style=dashed, color=red]",
                            origin_node_id.0, port_origin, node.id.0, port_user
                        )?;
                    }
                    _ => unimplemented!(),
                }
            }
        }
        writeln!(out, "}}")
    }
}

impl<S> PartialEq for NodeCtxt<S> {
    fn eq(&self, other: &NodeCtxt<S>) -> bool {
        ptr::eq(self, other)
    }
}

#[derive(Clone, Copy, PartialEq)]
pub struct Node<'g, S> {
    ctxt: &'g NodeCtxt<S>,
    id: NodeId,
}

impl<'g, S: fmt::Debug> fmt::Debug for Node<'g, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.data().kind)
    }
}

impl<'g, S> Node<'g, S> {
    pub fn data(&self) -> Ref<'g, NodeData<S>> {
        self.ctxt.node_data(self.id)
    }

    pub fn kind(&self) -> Ref<'g, NodeKind<S>> {
        Ref::map(self.ctxt.node_data(self.id), |node_data| &node_data.kind)
    }
}

impl<'g, S: Sig + Copy> Node<'g, S> {
    pub fn val_in(&self, port: usize) -> ValUser<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.val_ins);
        ValUser(self.ctxt.user_ref(UserId::In {
            node: self.id,
            index: port,
        }))
    }

    pub fn val_out(&self, port: usize) -> ValOrigin<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.val_outs);
        ValOrigin(self.ctxt.origin_ref(OriginId::Out {
            node: self.id,
            index: port,
        }))
    }

    pub fn st_in(&self, port: usize) -> StUser<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.st_ins);
        StUser(self.ctxt.user_ref(UserId::In {
            node: self.id,
            index: sig.val_ins + port,
        }))
    }

    pub fn st_out(&self, port: usize) -> StOrigin<'g, S> {
        let sig = self.data().sig();
        assert!(port < sig.st_outs);
        StOrigin(self.ctxt.origin_ref(OriginId::Out {
            node: self.id,
            index: sig.val_outs + port,
        }))
    }
}

#[derive(Copy, Clone, PartialEq)]
pub struct User<'g, S> {
    ctxt: &'g NodeCtxt<S>,
    user_id: UserId,
}

impl<'g, S: fmt::Debug> fmt::Debug for User<'g, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.user_id)
    }
}

impl<'g, S> User<'g, S> {
    pub fn id(&self) -> UserId {
        self.user_id
    }

    pub fn data(&self) -> Ref<'g, UserData> {
        self.ctxt.user_data(self.user_id)
    }

    pub fn origin(&self) -> Origin<'g, S> {
        let origin_id = self.data().origin.get().unwrap();
        self.ctxt.origin_ref(origin_id)
    }
}

#[derive(Copy, Clone, PartialEq)]
pub struct Origin<'g, S> {
    ctxt: &'g NodeCtxt<S>,
    origin_id: OriginId,
}

impl<'g, S: fmt::Debug> fmt::Debug for Origin<'g, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.origin_id)
    }
}

impl<'g, S> Origin<'g, S> {
    pub fn id(&self) -> OriginId {
        self.origin_id
    }

    pub fn data(&self) -> Ref<'g, OriginData> {
        self.ctxt.origin_data(self.origin_id)
    }

    pub fn producer(&self) -> Node<'g, S> {
        match self.origin_id {
            OriginId::Out { node, .. } => self.ctxt.node_ref(node),
            _ => unimplemented!(),
        }
    }

    pub fn users(&self) -> Users<'g, S> {
        let user_ref = |user_id| self.ctxt.user_ref(user_id);
        Users {
            first_and_last: self
                .data()
                .users
                .get()
                .map(|users| (user_ref(users.first), user_ref(users.last))),
        }
    }
}

pub struct Users<'g, S> {
    first_and_last: Option<(User<'g, S>, User<'g, S>)>,
}

impl<'g, S> Iterator for Users<'g, S> {
    type Item = User<'g, S>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.first_and_last.take() {
            Some((first, last)) => {
                if first.id() != last.id() {
                    if let Some(next_user) = first.data().next_user.get() {
                        self.first_and_last = Some((first.ctxt.user_ref(next_user), last));
                    }
                }
                Some(first)
            }
            None => None,
        }
    }
}

impl<'g, S> DoubleEndedIterator for Users<'g, S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.first_and_last.take() {
            Some((first, last)) => {
                if first.id() != last.id() {
                    if let Some(prev_user) = last.data().prev_user.get() {
                        self.first_and_last = Some((first, last.ctxt.user_ref(prev_user)));
                    }
                }
                Some(last)
            }
            None => None,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct ValUser<'g, S>(User<'g, S>);

impl<'g, S> ValUser<'g, S> {
    fn id(&self) -> UserId {
        self.0.id()
    }

    fn connect(&self, val_origin: ValOrigin<'g, S>) {
        assert!(self.0.ctxt == val_origin.0.ctxt);
        self.0.ctxt.connect_ports(self.id(), val_origin.id());
    }

    pub fn origin(&self) -> ValOrigin<'g, S> {
        ValOrigin(self.0.origin())
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct StUser<'g, S>(User<'g, S>);

impl<'g, S> StUser<'g, S> {
    fn id(&self) -> UserId {
        self.0.id()
    }

    fn connect(&self, st_origin: StOrigin<'g, S>) {
        assert!(self.0.ctxt == st_origin.0.ctxt);
        self.0.ctxt.connect_ports(self.id(), st_origin.id());
    }

    pub fn origin(&self) -> StOrigin<'g, S> {
        StOrigin(self.0.origin())
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct ValOrigin<'g, S>(Origin<'g, S>);

impl<'g, S> ValOrigin<'g, S> {
    fn id(&self) -> OriginId {
        self.0.id()
    }

    fn connect(&self, val_user: ValUser<'g, S>) {
        assert!(self.0.ctxt == val_user.0.ctxt);
        self.0.ctxt.connect_ports(val_user.id(), self.id());
    }

    pub fn users(&self) -> impl DoubleEndedIterator<Item = ValUser<'g, S>> {
        self.0.users().map(ValUser)
    }

    pub fn producer(&self) -> Node<'g, S> {
        self.0.producer()
    }
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct StOrigin<'g, S>(Origin<'g, S>);

impl<'g, S> StOrigin<'g, S> {
    fn id(&self) -> OriginId {
        self.0.id()
    }

    fn connect(&self, st_user: StUser<'g, S>) {
        assert!(self.0.ctxt == st_user.0.ctxt);
        self.0.ctxt.connect_ports(st_user.id(), self.id());
    }

    pub fn users(&self) -> impl DoubleEndedIterator<Item = StUser<'g, S>> {
        self.0.users().map(StUser)
    }

    pub fn producer(&self) -> Node<'g, S> {
        self.0.producer()
    }
}

#[cfg(test)]
mod test {
    use super::{NodeCtxt, NodeKind, UserId, OriginId, Sig, SigS};

    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum TestData {
        Lit(u32),
        Neg,
        St,
        BinAdd,
        BinSub,
        LoadOffset,
        Load,
        Store,
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
                TestData::BinAdd | TestData::BinSub => SigS {
                    val_ins: 2,
                    val_outs: 1,
                    ..SigS::default()
                },
                TestData::LoadOffset => SigS {
                    val_ins: 2,
                    val_outs: 1,
                    st_ins: 1,
                    st_outs: 1,
                    ..SigS::default()
                },
                TestData::Load => SigS {
                    val_ins: 1,
                    val_outs: 1,
                    st_ins: 1,
                    st_outs: 0,
                    ..SigS::default()
                },
                TestData::Store => SigS {
                    val_ins: 2,
                    val_outs: 0,
                    st_ins: 1,
                    st_outs: 1,
                    ..SigS::default()
                },
            }
        }
    }

    #[test]
    fn create_single_node() {
        let ncx = NodeCtxt::new();
        let n0 = ncx.create_node(NodeKind::Op(TestData::Lit(0)));
        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());
    }

    #[test]
    fn create_node_with_an_input() {
        let ncx = NodeCtxt::new();
        let n0 = ncx.create_node(NodeKind::Op(TestData::Lit(0)));
        let n1 = ncx.create_node(NodeKind::Op(TestData::Neg));

        ncx.connect_ports(
            UserId::In { node: n1, index: 0 },
            OriginId::Out { node: n0, index: 0 },
        );

        assert_eq!(
            Some(n0),
            ncx.node_data(n1).ins[0].origin.get().unwrap().node_id()
        );
    }

    #[test]
    fn create_node_with_an_input_using_builder() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(0));
        let n1 = ncx.mk_node(TestData::Neg);
        n1.val_in(0).connect(n0.val_out(0));

        assert_eq!(
            Some(n0.id),
            n1.data().ins[0].origin.get().unwrap().node_id()
        );
        assert_eq!(n0.val_out(0), n1.val_in(0).origin());
    }

    #[test]
    fn create_node_with_input_ports() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.create_node(NodeKind::Op(TestData::Lit(2)));

        assert_eq!(0, ncx.node_data(n0).ins.len());
        assert_eq!(1, ncx.node_data(n0).outs.len());

        let n1 = ncx.create_node(NodeKind::Op(TestData::Lit(3)));

        assert_eq!(0, ncx.node_data(n1).ins.len());
        assert_eq!(1, ncx.node_data(n1).outs.len());

        let n2 = ncx.create_node(NodeKind::Op(TestData::BinAdd));

        ncx.connect_ports(
            UserId::In { node: n2, index: 0 },
            OriginId::Out { node: n0, index: 0 },
        );
        ncx.connect_ports(
            UserId::In { node: n2, index: 1 },
            OriginId::Out { node: n1, index: 0 },
        );

        assert_eq!(2, ncx.node_data(n2).ins.len());
        assert_eq!(1, ncx.node_data(n2).outs.len());

        assert_eq!(
            Some(n2),
            ncx.node_data(n0).outs[0]
                .users
                .get()
                .unwrap()
                .first
                .node_id()
        );
        assert_eq!(
            Some(n2),
            ncx.node_data(n0).outs[0]
                .users
                .get()
                .unwrap()
                .last
                .node_id()
        );
        assert_eq!(
            Some(n2),
            ncx.node_data(n1).outs[0]
                .users
                .get()
                .unwrap()
                .first
                .node_id()
        );
        assert_eq!(
            Some(n2),
            ncx.node_data(n1).outs[0]
                .users
                .get()
                .unwrap()
                .last
                .node_id()
        );
    }

    #[test]
    fn create_node_operands_and_states_using_builder_single() {
        let ncx = NodeCtxt::new();

        let n0 = ncx.mk_node(TestData::Lit(2));
        let n1 = ncx.mk_node(TestData::Lit(3));
        let n2 = ncx.mk_node(TestData::St);

        let n3 = ncx.mk_node(TestData::LoadOffset);

        n3.val_in(0).connect(n0.val_out(0));
        n3.val_in(1).connect(n1.val_out(0));
        n3.st_in(0).connect(n2.st_out(0));

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
        // TODO: state port users
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
    fn users_double_ended_iterator() {
        // TODO: state port users
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
        assert_eq!(Some(n3.val_in(0)), users.next_back());
        assert_eq!(Some(n2.val_in(0)), users.next_back());
        assert_eq!(None, users.next());
        assert_eq!(None, users.next_back());
    }

    #[test]
    #[should_panic]
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

    #[test]
    fn printing_load_store_nodes() {
        let ncx = NodeCtxt::new();

        let n_x = ncx.mk_node(TestData::Lit(100));
        let n_y = ncx.mk_node(TestData::Lit(104));
        let n_4 = ncx.mk_node(TestData::Lit(4));
        let n_5 = ncx.mk_node(TestData::Lit(5));
        let n_s = ncx.mk_node(TestData::St);

        let n_l1 = ncx
            .node_builder(TestData::Load)
            .operand(n_x.val_out(0))
            .state(n_s.st_out(0))
            .finish();

        let n_add_4 = ncx
            .node_builder(TestData::BinAdd)
            .operand(n_l1.val_out(0))
            .operand(n_4.val_out(0))
            .finish();

        let n_store1 = ncx
            .node_builder(TestData::Store)
            .operand(n_x.val_out(0))
            .operand(n_add_4.val_out(0))
            .state(n_s.st_out(0))
            .finish();

        let n_l2 = ncx
            .node_builder(TestData::Load)
            .operand(n_y.val_out(0))
            .state(n_store1.st_out(0))
            .finish();

        let n_add_5 = ncx
            .node_builder(TestData::BinAdd)
            .operand(n_l2.val_out(0))
            .operand(n_5.val_out(0))
            .finish();

        let _ = ncx
            .node_builder(TestData::Store)
            .operand(n_y.val_out(0))
            .operand(n_add_5.val_out(0))
            .state(n_store1.st_out(0))
            .finish();

        let mut buffer = Vec::new();
        ncx.print(&mut buffer).unwrap();
        let content = String::from_utf8(buffer).unwrap();
        assert_eq!(
            content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{Lit(100)}|{<o0>0}}"]
    n1 [label="{{Lit(104)}|{<o0>0}}"]
    n2 [label="{{Lit(4)}|{<o0>0}}"]
    n3 [label="{{Lit(5)}|{<o0>0}}"]
    n4 [label="{{St}|{<o0>0}}"]
    n5 [label="{{<i0>0|<i1>1}|{Load}|{<o0>0}}"]
    n0:o0 -> n5:i0 [color=blue]
    n4:o0 -> n5:i1 [style=dashed, color=red]
    n6 [label="{{<i0>0|<i1>1}|{BinAdd}|{<o0>0}}"]
    n5:o0 -> n6:i0 [color=blue]
    n2:o0 -> n6:i1 [color=blue]
    n7 [label="{{<i0>0|<i1>1|<i2>2}|{Store}|{<o0>0}}"]
    n0:o0 -> n7:i0 [color=blue]
    n6:o0 -> n7:i1 [color=blue]
    n4:o0 -> n7:i2 [style=dashed, color=red]
    n8 [label="{{<i0>0|<i1>1}|{Load}|{<o0>0}}"]
    n1:o0 -> n8:i0 [color=blue]
    n7:o0 -> n8:i1 [style=dashed, color=red]
    n9 [label="{{<i0>0|<i1>1}|{BinAdd}|{<o0>0}}"]
    n8:o0 -> n9:i0 [color=blue]
    n3:o0 -> n9:i1 [color=blue]
    n10 [label="{{<i0>0|<i1>1|<i2>2}|{Store}|{<o0>0}}"]
    n1:o0 -> n10:i0 [color=blue]
    n9:o0 -> n10:i1 [color=blue]
    n7:o0 -> n10:i2 [style=dashed, color=red]
}
"#
        );
    }

    #[test]
    fn manually_connecting_ports() {
        let ncx = NodeCtxt::new();

        let lit_a = ncx.mk_node(TestData::Lit(2));
        let lit_b = ncx.mk_node(TestData::Lit(3));
        let add = ncx.mk_node(TestData::BinAdd);

        add.val_in(0).connect(lit_a.val_out(0));
        add.val_in(1).connect(lit_b.val_out(0));

        let mut users = lit_a.val_out(0).users();

        assert_eq!(Some(add.val_in(0)), users.next());
        assert_eq!(None, users.next());

        let mut users = lit_b.val_out(0).users();

        assert_eq!(Some(add.val_in(1)), users.next());
        assert_eq!(None, users.next());
    }
}
