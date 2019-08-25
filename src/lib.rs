//! Oxide uses the same interning architecture as the Rust compiler's for
//! avoiding duplication of equivalent nodes.

#![feature(hash_raw_entry)]

use arena::DroplessArena;
use std::{
    borrow::Borrow,
    cell::RefCell,
    cmp::Ordering,
    collections::{hash_map::RawEntryMut, HashMap},
    hash::{BuildHasher, Hash, Hasher},
    ptr,
};

#[derive(Clone, Copy)]
struct Interned<'ncx, T: ?Sized>(&'ncx T);

impl<'ncx> PartialEq for Interned<'ncx, NodeS<'ncx>> {
    fn eq(&self, other: &Interned<'ncx, NodeS<'ncx>>) -> bool {
        self.0.kind == other.0.kind
    }
}

impl<'ncx> Eq for Interned<'ncx, NodeS<'ncx>> {}

impl<'ncx> Hash for Interned<'ncx, NodeS<'ncx>> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.kind.hash(state);
    }
}

impl<'ncx> Borrow<NodeKind<'ncx>> for Interned<'ncx, NodeS<'ncx>> {
    fn borrow<'a>(&'a self) -> &'a NodeKind<'ncx> {
        &self.0.kind
    }
}

type Node<'ncx> = &'ncx NodeS<'ncx>;

#[derive(Debug, Copy, Clone, PartialEq, Default)]
struct Sig {
    val_ins: usize,
    val_outs: usize,
    st_ins: usize,
    st_outs: usize,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct ValIn<'ncx> {
    proj_index: usize,
    origin: Node<'ncx>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum BinOp {
    Add,
    Sub,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum UnOp {
    Neg,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum NodeKind<'ncx> {
    Lit(u128),
    Unary(UnOp, ValIn<'ncx>),
    Bin(BinOp, ValIn<'ncx>, ValIn<'ncx>),
}

trait Signature {
    fn sig(&self) -> Sig;
}

impl<'ncx> Signature for NodeKind<'ncx> {
    fn sig(&self) -> Sig {
        match self {
            NodeKind::Lit(..) => Sig {
                val_outs: 1,
                ..Default::default()
            },
            NodeKind::Unary(..) => Sig {
                val_ins: 1,
                val_outs: 1,
                ..Default::default()
            },
            NodeKind::Bin(..) => Sig {
                val_ins: 2,
                val_outs: 1,
                ..Default::default()
            },
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct NodeS<'ncx> {
    kind: NodeKind<'ncx>,
}

impl<'ncx> Ord for NodeS<'ncx> {
    fn cmp(&self, other: &NodeS<'ncx>) -> Ordering {
        self.kind.cmp(&other.kind)
    }
}

impl<'ncx> PartialOrd for NodeS<'ncx> {
    fn partial_cmp(&self, other: &NodeS<'ncx>) -> Option<Ordering> {
        Some(self.kind.cmp(&other.kind))
    }
}

impl<'ncx> PartialEq for NodeS<'ncx> {
    fn eq(&self, other: &NodeS<'ncx>) -> bool {
        ptr::eq(self, other)
    }
}

impl<'ncx> Eq for NodeS<'ncx> {}

impl<'ncx> Hash for NodeS<'ncx> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self as *const NodeS<'_>).hash(state)
    }
}

struct InternedHashSet<K: Eq + Hash> {
    set: RefCell<HashMap<K, ()>>,
}

impl<K: Eq + Hash + Copy> InternedHashSet<K> {
    fn new() -> InternedHashSet<K> {
        InternedHashSet {
            set: Default::default(),
        }
    }

    fn intern<Q>(&self, value: Q, make: impl FnOnce(Q) -> K) -> K
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let mut set = self.set.borrow_mut();
        let hash = {
            let mut hasher = (*set).hasher().build_hasher();
            value.hash(&mut hasher);
            hasher.finish()
        };

        let entry = set.raw_entry_mut().from_key_hashed_nocheck(hash, &value);

        match entry {
            RawEntryMut::Occupied(e) => *e.key(),
            RawEntryMut::Vacant(e) => {
                let val = make(value);
                e.insert_hashed_nocheck(hash, val, ());
                val
            }
        }
    }
}

type InternedSet<'ncx, T> = InternedHashSet<Interned<'ncx, T>>;

struct CtxtInterners<'ncx> {
    arena: &'ncx DroplessArena,
    nodes: InternedSet<'ncx, NodeS<'ncx>>,
}

impl<'ncx> CtxtInterners<'ncx> {
    fn new(arena: &'ncx DroplessArena) -> CtxtInterners<'ncx> {
        CtxtInterners {
            arena,
            nodes: InternedSet::new(),
        }
    }

    fn intern_node(&self, node_kind: NodeKind<'ncx>) -> Node<'ncx> {
        let Interned(node_ref) = self.nodes.intern(node_kind, |node_kind| {
            Interned(self.arena.alloc(NodeS { kind: node_kind }))
        });
        node_ref
    }
}

#[derive(Clone, Copy)]
struct NodeCtxt<'ncx> {
    gcx: &'ncx GlobalCtxt<'ncx>,
}

impl<'ncx> NodeCtxt<'ncx> {
    fn mk_node(&self, node_kind: NodeKind<'ncx>) -> Node<'ncx> {
        self.gcx.interners.intern_node(node_kind)
    }

    fn mk_lit(&self, value: u128) -> Node<'ncx> {
        self.mk_node(NodeKind::Lit(value))
    }

    fn mk_add(&self, lhs: Node<'ncx>, rhs: Node<'ncx>) -> Node<'ncx> {
        self.mk_node(NodeKind::Bin(
            BinOp::Add,
            ValIn {
                proj_index: 0,
                origin: lhs,
            },
            ValIn {
                proj_index: 0,
                origin: rhs,
            },
        ))
    }
}

struct GlobalCtxt<'ncx> {
    interners: CtxtInterners<'ncx>,
}

impl<'ncx> GlobalCtxt<'ncx> {
    fn new(arena: &'ncx DroplessArena) -> GlobalCtxt<'ncx> {
        GlobalCtxt {
            interners: CtxtInterners::new(arena),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{BinOp, GlobalCtxt, NodeCtxt, NodeKind};
    use arena::DroplessArena;
    use std::ptr;

    #[test]
    fn reuse_nodes_that_compare_equal() {
        let arena = DroplessArena::default();
        let gcx = GlobalCtxt::new(&arena);
        let ncx = NodeCtxt { gcx: &gcx };

        let n0 = ncx.mk_lit(0);
        let n1 = ncx.mk_lit(1);
        let n2 = ncx.mk_lit(0);

        assert_ne!(n0, n1);
        assert_ne!(n1, n2);
        assert_eq!(n0, n2);

        assert!(!ptr::eq(n0, n1));
        assert!(!ptr::eq(n1, n2));
        assert!(ptr::eq(n0, n2));

        let n3 = ncx.mk_add(n0, n1);
        let n4 = ncx.mk_add(n1, n0);
        let n5 = ncx.mk_add(n0, n1);

        assert_ne!(n3, n4);
        assert_ne!(n4, n5);
        assert_eq!(n3, n5);

        assert!(!ptr::eq(n3, n4));
        assert!(!ptr::eq(n4, n5));
        assert!(ptr::eq(n3, n5));
    }
}
