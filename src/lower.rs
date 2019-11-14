use crate::rvsdg::{Node, NodeCtxt, NodeId, NodeKind, Sig, SigS, ValOrigin};
use std::{collections::HashMap, hash::Hash};

trait Lower<'g, 'h: 'g, S: Sig, T: Sig> {
    fn lower(&mut self, node: Node<'h, S>, ncx: &'g NodeCtxt<T>) -> Node<'g, T>;
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Hir {
    I32(i32),
    Usize(usize),
    Array(Vec<i32>),
    GlobalState,
    Subscript,
    Add,
    Sub,
    Mul,
    Div,
    Le,
    Lt,
    Ge,
    Gt,
    And,
    Or,
    Xor,
    Not,
    Neg,
    Shl,
    Shr,
    Mod,
}

impl Sig for Hir {
    fn sig(&self) -> SigS {
        match self {
            Hir::I32(..) | Hir::Usize(..) | Hir::Array(..) => SigS {
                val_outs: 1,
                ..SigS::default()
            },
            Hir::GlobalState => SigS {
                st_outs: 1,
                ..SigS::default()
            },
            Hir::Add
            | Hir::Subscript
            | Hir::Mul
            | Hir::Sub
            | Hir::Div
            | Hir::Le
            | Hir::Lt
            | Hir::Ge
            | Hir::Gt
            | Hir::And
            | Hir::Or
            | Hir::Xor
            | Hir::Shl
            | Hir::Shr
            | Hir::Mod => SigS {
                val_ins: 2,
                val_outs: 1,
                ..SigS::default()
            },
            Hir::Not | Hir::Neg => SigS {
                val_ins: 1,
                val_outs: 1,
                ..SigS::default()
            },
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Lir {
    I32(i32),
    Usize(usize),
    Alloc,
    Free,
    GlobalState,
    Load,
    Store,
    Add,
    Sub,
    Mul,
    DivMod,
    Cmp,
    BitAnd,
    BitOr,
    BitXor,
    BitNot,
    Shl,
    Shr,
    Inc,
    Dec,
    Merge {
        num_of_values: usize,
        num_of_states: usize,
    },
}

impl Sig for Lir {
    fn sig(&self) -> SigS {
        match self {
            Lir::I32(..) | Lir::Usize(..) => SigS {
                val_outs: 1,
                ..SigS::default()
            },
            Lir::Alloc => SigS {
                val_ins: 1,
                val_outs: 1,
                st_outs: 1,
                ..SigS::default()
            },
            Lir::Free => SigS {
                val_ins: 1,
                ..SigS::default()
            },
            Lir::GlobalState => SigS {
                st_outs: 1,
                ..SigS::default()
            },
            Lir::Add
            | Lir::Mul
            | Lir::Sub
            | Lir::Cmp
            | Lir::BitAnd
            | Lir::BitOr
            | Lir::BitXor
            | Lir::Shl
            | Lir::Shr
            | Lir::BitNot => SigS {
                val_ins: 2,
                val_outs: 1,
                ..SigS::default()
            },
            Lir::DivMod => SigS {
                val_ins: 2,
                val_outs: 2,
                ..SigS::default()
            },
            Lir::Inc | Lir::Dec => SigS {
                val_ins: 1,
                val_outs: 1,
                ..SigS::default()
            },
            Lir::Load => SigS {
                val_ins: 1,
                st_ins: 1,
                val_outs: 1,
                ..SigS::default()
            },
            Lir::Store => SigS {
                val_ins: 2,
                st_ins: 1,
                st_outs: 1,
                ..SigS::default()
            },
            Lir::Merge {
                num_of_values,
                num_of_states,
            } => SigS {
                val_ins: *num_of_values,
                val_outs: *num_of_values,
                st_ins: *num_of_states,
                st_outs: 1,
                ..SigS::default()
            },
        }
    }
}

struct HirToLir {
    visited: HashMap<NodeId, NodeId>,
}

impl HirToLir {
    fn new() -> HirToLir {
        HirToLir {
            visited: HashMap::new(),
        }
    }
}

impl<'g, 'h: 'g> Lower<'g, 'h, Hir, Lir> for HirToLir {
    fn lower(&mut self, node: Node<'h, Hir>, ncx: &'g NodeCtxt<Lir>) -> Node<'g, Lir> {
        if let Some(existing_node_id) = self.visited.get(&node.id()) {
            return ncx.node_ref(*existing_node_id);
        }
        let node_kind = &*node.kind();
        let op = match node_kind {
            NodeKind::Op(op) => op,
            _ => unimplemented!(),
        };
        let lir_node = match op {
            Hir::I32(val) => ncx.mk_node(Lir::I32(*val)),
            Hir::Usize(val) => ncx.mk_node(Lir::Usize(*val)),
            Hir::Array(elems) => {
                // Creates an allocation node for the array size, creates a store node for every
                // array element, then merge all stores' state outputs.
                let element_size_in_bytes = 4usize;
                let array_length = ncx.mk_node(Lir::Usize(elems.len()));

                let array_size_node = ncx
                    .node_builder(Lir::Mul)
                    .operand(array_length.val_out(0))
                    .operand(ncx.mk_node(Lir::Usize(element_size_in_bytes)).val_out(0))
                    .finish();

                let alloc_node = ncx
                    .node_builder(Lir::Alloc)
                    .operand(array_size_node.val_out(0))
                    .finish();

                let mut merge_node_builder = ncx.node_builder(Lir::Merge {
                    num_of_values: 1, // the array base address
                    num_of_states: elems.len(),
                });

                for (i, &val) in elems.iter().enumerate() {
                    let elem_byte_offset = ncx
                        .node_builder(Lir::Mul)
                        .operand(ncx.mk_node(Lir::Usize(i)).val_out(0))
                        .operand(ncx.mk_node(Lir::Usize(element_size_in_bytes)).val_out(0))
                        .finish();

                    let elem_addr = ncx
                        .node_builder(Lir::Add)
                        .operand(alloc_node.val_out(0))
                        .operand(elem_byte_offset.val_out(0))
                        .finish();

                    let store_node = ncx
                        .node_builder(Lir::Store)
                        .operand(elem_addr.val_out(0))
                        .operand(ncx.mk_node(Lir::I32(val)).val_out(0))
                        .state(alloc_node.st_out(0))
                        .finish();

                    merge_node_builder = merge_node_builder.state(store_node.st_out(0));
                }

                let merge_node = merge_node_builder.operand(alloc_node.val_out(0)).finish();

                merge_node
            }
            Hir::GlobalState => ncx.mk_node(Lir::GlobalState),
            Hir::Subscript => {
                let base = self.lower(node.val_in(0).origin().producer(), ncx);
                let index = self.lower(node.val_in(1).origin().producer(), ncx);
                let state_port = if base.kind().sig().st_outs > 0 {
                    base.st_out(0)
                } else {
                    ncx.mk_node(Lir::GlobalState).st_out(0)
                };

                let offset = ncx
                    .node_builder(Lir::Mul)
                    .operand(index.val_out(0))
                    .operand(ncx.mk_node(Lir::Usize(4)).val_out(0))
                    .finish();

                let base_offset = ncx
                    .node_builder(Lir::Add)
                    .operand(base.val_out(0))
                    .operand(offset.val_out(0))
                    .finish();

                ncx.node_builder(Lir::Load)
                    .operand(base_offset.val_out(0))
                    .state(state_port)
                    .finish()
            }
            Hir::Add => {
                let lhs = self.lower(node.val_in(0).origin().producer(), ncx);
                let rhs = self.lower(node.val_in(1).origin().producer(), ncx);

                ncx.node_builder(Lir::Add)
                    .operand(lhs.val_out(0))
                    .operand(rhs.val_out(0))
                    .finish()
            }
            Hir::Sub => {
                let lhs = self.lower(node.val_in(0).origin().producer(), ncx);
                let rhs = self.lower(node.val_in(1).origin().producer(), ncx);

                ncx.node_builder(Lir::Sub)
                    .operand(lhs.val_out(0))
                    .operand(rhs.val_out(0))
                    .finish()
            }
            Hir::Mul => {
                let lhs = self.lower(node.val_in(0).origin().producer(), ncx);
                let rhs = self.lower(node.val_in(1).origin().producer(), ncx);

                ncx.node_builder(Lir::Mul)
                    .operand(lhs.val_out(0))
                    .operand(rhs.val_out(0))
                    .finish()
            }
            _ => unimplemented!(),
        };
        self.visited.insert(node.id(), lir_node.id());
        lir_node
    }
}

struct ConstFoldOpt<'graph, S> {
    memory_stack: Vec<u8>,
    alloc_stack_addrs: HashMap<ValOrigin<'graph, S>, usize>,
}

impl<'graph, S> ConstFoldOpt<'graph, S> {
    fn new() -> ConstFoldOpt<'graph, S>
    where
        S: Eq + Hash,
    {
        ConstFoldOpt {
            memory_stack: vec![],
            alloc_stack_addrs: HashMap::new(),
        }
    }
}

impl<'g, 'h: 'g> Lower<'g, 'h, Lir, Lir> for ConstFoldOpt<'g, Lir> {
    fn lower(&mut self, node: Node<'h, Lir>, ncx: &'g NodeCtxt<Lir>) -> Node<'g, Lir> {
        let op = match &*node.kind() {
            NodeKind::Op(op) => op.clone(),
            _ => unimplemented!(),
        };
        // TODO: states = self.lower in st_ins
        match op {
            Lir::I32(val) => ncx.mk_node(Lir::I32(val)),
            Lir::Usize(val) => ncx.mk_node(Lir::Usize(val)),
            Lir::Alloc => {
                let alloc_size_node = self.lower(node.val_in(0).origin().producer(), ncx);

                match *alloc_size_node.kind() {
                    NodeKind::Op(Lir::Usize(val)) => {
                        let cur_sp = self.memory_stack.len();
                        self.memory_stack.resize(cur_sp + val, 0);
                        self.alloc_stack_addrs.insert(node.val_out(0), cur_sp);
                    }
                    _ => {}
                }

                ncx.node_builder(Lir::Alloc)
                    .operand(alloc_size_node.val_out(0))
                    .finish()
            }
            Lir::Add => {
                let lhs = node.val_in(0).origin().producer();
                let rhs = node.val_in(1).origin().producer();

                match (lhs.kind().clone(), rhs.kind().clone()) {
                    (_, NodeKind::Op(Lir::I32(0))) => {
                        self.lower(lhs, ncx)
                    }
                    (NodeKind::Op(Lir::I32(0)), _) => {
                        self.lower(rhs, ncx)
                    }
                    (NodeKind::Op(Lir::I32(val_lhs)), NodeKind::Op(Lir::I32(val_rhs))) => {
                        ncx.mk_node(Lir::I32(val_lhs + val_rhs))
                    }
                    (_, NodeKind::Op(Lir::Usize(0))) => {
                        self.lower(lhs, ncx)
                    }
                    (NodeKind::Op(Lir::Usize(0)), _) => {
                        self.lower(rhs, ncx)
                    }
                    (NodeKind::Op(Lir::Usize(val_lhs)), NodeKind::Op(Lir::Usize(val_rhs))) => {
                        ncx.mk_node(Lir::Usize(val_lhs + val_rhs))
                    }
                    (NodeKind::Op(Lir::Usize(val)), NodeKind::Op(Lir::Alloc))
                        if self.alloc_stack_addrs.contains_key(&rhs.val_out(0)) =>
                    {
                        let stack_base_index = self.alloc_stack_addrs.get(&rhs.val_out(0)).unwrap();
                        ncx.mk_node(Lir::Usize(val + stack_base_index))
                    }
                    _ => {
                        let lhs = self.lower(node.val_in(0).origin().producer(), ncx);
                        let rhs = self.lower(node.val_in(1).origin().producer(), ncx);
                        let add_builder = ncx
                            .node_builder(Lir::Add)
                            .operand(lhs.val_out(0))
                            .operand(rhs.val_out(0));

                        let add = add_builder.finish();

                        add
                    }
                }
            }
            Lir::Mul => {
                let lhs = node.val_in(0).origin().producer();
                let rhs = node.val_in(1).origin().producer();

                match (lhs.kind().clone(), rhs.kind().clone()) {
                    (NodeKind::Op(Lir::I32(val_lhs)), NodeKind::Op(Lir::I32(val_rhs))) => {
                        ncx.mk_node(Lir::I32(val_lhs * val_rhs))
                    }
                    (NodeKind::Op(Lir::Usize(val_lhs)), NodeKind::Op(Lir::Usize(val_rhs))) => {
                        ncx.mk_node(Lir::Usize(val_lhs * val_rhs))
                    }
                    _ => {
                        let lhs = self.lower(lhs, ncx);
                        let rhs = self.lower(rhs, ncx);
                        ncx.node_builder(Lir::Add)
                            .operand(lhs.val_out(0))
                            .operand(rhs.val_out(0))
                            .finish()
                    }
                }
            }
            _ => {
                let mut node_builder = ncx.node_builder(op.clone());
                for i in 0..op.sig().st_ins {
                    let opi = self.lower(node.st_in(i).origin().producer(), ncx);
                    node_builder = node_builder.state(opi.st_out(0));
                }
                for i in 0..op.sig().val_ins {
                    let opi = self.lower(node.val_in(i).origin().producer(), ncx);
                    node_builder = node_builder.operand(opi.val_out(0));
                }
                node_builder.finish()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{ConstFoldOpt, Hir, HirToLir, Lower};
    use crate::rvsdg::{Node, NodeCtxt, NodeKind, Sig, SigS};
    use std::io;

    #[test]
    fn hir_to_lir() {
        let hir = NodeCtxt::new();

        let subscript = hir
            .node_builder(Hir::Subscript)
            .operand(hir.mk_node(Hir::Usize(110)).val_out(0))
            .operand(hir.mk_node(Hir::Usize(7)).val_out(0))
            .finish();

        let mut hir_buffer = Vec::new();
        hir.print(&mut hir_buffer).unwrap();
        let hir_content = String::from_utf8(hir_buffer).unwrap();

        assert_eq!(
            hir_content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{Usize(110)}|{<o0>0}}"]
    n1 [label="{{Usize(7)}|{<o0>0}}"]
    n2 [label="{{<i0>0|<i1>1}|{Subscript}|{<o0>0}}"]
    n0:o0 -> n2:i0 [color=blue]
    n1:o0 -> n2:i1 [color=blue]
}
"#
        );

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::new();
        hir_to_lir.lower(subscript, &lir);

        let mut lir_buffer = Vec::new();
        lir.print(&mut lir_buffer).unwrap();
        let lir_content = String::from_utf8(lir_buffer).unwrap();

        assert_eq!(
            lir_content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{Usize(110)}|{<o0>0}}"]
    n1 [label="{{Usize(7)}|{<o0>0}}"]
    n2 [label="{{GlobalState}|{<o0>0}}"]
    n3 [label="{{Usize(4)}|{<o0>0}}"]
    n4 [label="{{<i0>0|<i1>1}|{Mul}|{<o0>0}}"]
    n1:o0 -> n4:i0 [color=blue]
    n3:o0 -> n4:i1 [color=blue]
    n5 [label="{{<i0>0|<i1>1}|{Add}|{<o0>0}}"]
    n0:o0 -> n5:i0 [color=blue]
    n4:o0 -> n5:i1 [color=blue]
    n6 [label="{{<i0>0|<i1>1}|{Load}|{<o0>0}}"]
    n5:o0 -> n6:i0 [color=blue]
    n2:o0 -> n6:i1 [style=dashed, color=red]
}
"#
        );
    }

    #[test]
    fn constant_folding() {
        #[derive(Clone, PartialEq, Eq, Hash, Debug)]
        enum Ir {
            Lit(i32),
            Var(&'static str),
            Add,
        }

        impl Sig for Ir {
            fn sig(&self) -> SigS {
                match self {
                    Ir::Lit(..) => SigS {
                        val_outs: 1,
                        ..<_>::default()
                    },
                    Ir::Var(..) => SigS {
                        val_outs: 1,
                        ..<_>::default()
                    },
                    Ir::Add => SigS {
                        val_ins: 2,
                        val_outs: 1,
                        ..<_>::default()
                    },
                }
            }
        }

        struct ConstFoldOpt;

        impl<'g, 'h: 'g> Lower<'g, 'h, Ir, Ir> for ConstFoldOpt {
            fn lower(&mut self, node: Node<'h, Ir>, ncx: &'g NodeCtxt<Ir>) -> Node<'g, Ir> {
                let op = match node.kind().clone() {
                    NodeKind::Op(op) => op,
                    _ => unimplemented!(),
                };
                match op {
                    Ir::Lit(lit) => ncx.mk_node(Ir::Lit(lit)),
                    Ir::Var(var) => ncx.mk_node(Ir::Var(var)),
                    Ir::Add => {
                        let lhs = node.val_in(0).origin().producer();
                        let rhs = node.val_in(1).origin().producer();

                        match (lhs.kind().clone(), rhs.kind().clone()) {
                            (NodeKind::Op(Ir::Lit(val_lhs)), NodeKind::Op(Ir::Lit(val_rhs))) => {
                                ncx.mk_node(Ir::Lit(val_lhs + val_rhs))
                            }
                            _ => {
                                let lhs = self.lower(lhs, ncx);
                                let rhs = self.lower(rhs, ncx);
                                ncx.node_builder(Ir::Add)
                                    .operand(lhs.val_out(0))
                                    .operand(rhs.val_out(0))
                                    .finish()
                            }
                        }
                    }
                }
            }
        }

        let ncx_noopt = NodeCtxt::new();

        let n0 = ncx_noopt
            .node_builder(Ir::Add)
            .operand(ncx_noopt.mk_node(Ir::Lit(2)).val_out(0))
            .operand(ncx_noopt.mk_node(Ir::Lit(3)).val_out(0))
            .finish();

        let n1 = ncx_noopt
            .node_builder(Ir::Add)
            .operand(n0.val_out(0))
            .operand(ncx_noopt.mk_node(Ir::Var("x")).val_out(0))
            .finish();

        let mut noopt_buffer = Vec::new();
        ncx_noopt.print(&mut noopt_buffer).unwrap();
        let noopt_content = String::from_utf8(noopt_buffer).unwrap();

        assert_eq!(
            noopt_content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{Lit(2)}|{<o0>0}}"]
    n1 [label="{{Lit(3)}|{<o0>0}}"]
    n2 [label="{{<i0>0|<i1>1}|{Add}|{<o0>0}}"]
    n0:o0 -> n2:i0 [color=blue]
    n1:o0 -> n2:i1 [color=blue]
    n3 [label="{{Var("x")}|{<o0>0}}"]
    n4 [label="{{<i0>0|<i1>1}|{Add}|{<o0>0}}"]
    n2:o0 -> n4:i0 [color=blue]
    n3:o0 -> n4:i1 [color=blue]
}
"#
        );

        let mut cfopt = ConstFoldOpt;
        let ncx_opt = NodeCtxt::new();

        cfopt.lower(n1, &ncx_opt);

        let mut opt_buffer = Vec::new();
        ncx_opt.print(&mut opt_buffer).unwrap();
        let opt_content = String::from_utf8(opt_buffer).unwrap();

        assert_eq!(
            opt_content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{Lit(5)}|{<o0>0}}"]
    n1 [label="{{Var("x")}|{<o0>0}}"]
    n2 [label="{{<i0>0|<i1>1}|{Add}|{<o0>0}}"]
    n0:o0 -> n2:i0 [color=blue]
    n1:o0 -> n2:i1 [color=blue]
}
"#
        );
    }

    #[test]
    fn array_10x42_to_stores() {
        use crate::rvsdg::NodeCtxtConfig;

        let hir = NodeCtxt::new();
        let arr = hir.mk_node(Hir::Array(vec![42; 10]));
        let subscript = hir
            .node_builder(Hir::Subscript)
            .operand(arr.val_out(0))
            .operand(hir.mk_node(Hir::Usize(1)).val_out(0))
            .finish();
        hir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-10x42-hir - nodes({}), edges({})",
            hir.num_nodes(),
            hir.num_edges()
        );

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::with_config(NodeCtxtConfig {
            opt_interning: false,
        });
        let merge = hir_to_lir.lower(subscript.clone(), &lir);
        lir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-10x42-lir - nodes({}), edges({})",
            lir.num_nodes(),
            lir.num_edges()
        );

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::with_config(NodeCtxtConfig {
            opt_interning: true,
        });
        let merge = hir_to_lir.lower(subscript, &lir);
        lir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-10x42-lir-valuenum - nodes({}), edges({})",
            lir.num_nodes(),
            lir.num_edges()
        );

        let lir_opt = NodeCtxt::new();
        let mut const_fold = ConstFoldOpt::new();
        let _ = const_fold.lower(merge, &lir_opt);
        lir_opt.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-10x42-lir-valuenum-constfold - nodes({}), edges({})",
            lir_opt.num_nodes(),
            lir_opt.num_edges()
        );
    }

    #[test]
    fn array_0to9_to_stores() {
        use crate::rvsdg::NodeCtxtConfig;

        {
            let hir = NodeCtxt::with_config(NodeCtxtConfig { opt_interning: false });
            let arr1 = hir.mk_node(Hir::Array((0..2).collect()));
            let arr2 = hir.mk_node(Hir::Array((0..2).collect()));
            let subscript1 = hir
                .node_builder(Hir::Subscript)
                .operand(arr1.val_out(0))
                .operand(hir.mk_node(Hir::Usize(1)).val_out(0))
                .finish();
            let subscript2 = hir
                .node_builder(Hir::Subscript)
                .operand(arr2.val_out(0))
                .operand(hir.mk_node(Hir::Usize(1)).val_out(0))
                .finish();
            let add = hir
                .node_builder(Hir::Add)
                .operand(subscript1.val_out(0))
                .operand(subscript2.val_out(0))
                .finish();
            hir.print(&mut io::stdout().lock()).unwrap();

            println!(
                "array-0to9-hir noopt - nodes({}), edges({})",
                hir.num_nodes(),
                hir.num_edges()
            );
        }

        let hir = NodeCtxt::new();
        let arr1 = hir.mk_node(Hir::Array((0..4).collect()));
        let arr2 = hir.mk_node(Hir::Array((0..4).collect()));
        let subscript1 = hir
            .node_builder(Hir::Subscript)
            .operand(arr1.val_out(0))
            .operand(hir.mk_node(Hir::Usize(1)).val_out(0))
            .finish();
        let subscript2 = hir
            .node_builder(Hir::Subscript)
            .operand(arr2.val_out(0))
            .operand(hir.mk_node(Hir::Usize(1)).val_out(0))
            .finish();
        let add = hir
            .node_builder(Hir::Add)
            .operand(subscript1.val_out(0))
            .operand(subscript2.val_out(0))
            .finish();
        hir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-0to9-hir noopt - nodes({}), edges({})",
            hir.num_nodes(),
            hir.num_edges()
        );

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::with_config(NodeCtxtConfig {
            opt_interning: false,
        });
        let merge = hir_to_lir.lower(add.clone(), &lir);
        lir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-0to9-lir - nodes({}), edges({})",
            lir.num_nodes(),
            lir.num_edges()
        );

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::with_config(NodeCtxtConfig {
            opt_interning: true,
        });
        let merge = hir_to_lir.lower(add, &lir);
        lir.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-0to9-lir-valuenum - nodes({}), edges({})",
            lir.num_nodes(),
            lir.num_edges()
        );

        let lir_opt1 = NodeCtxt::new();
        let lir_opt2 = NodeCtxt::new();

        let mut const_fold = ConstFoldOpt::new();
        let merge1 = const_fold.lower(merge, &lir_opt1);
        let _ = const_fold.lower(merge1, &lir_opt2);
        lir_opt2.print(&mut io::stdout().lock()).unwrap();

        println!(
            "array-0to9-lir-valuenum-constfold - nodes({}), edges({})",
            lir_opt2.num_nodes(),
            lir_opt2.num_edges()
        );
    }

    #[test]
    #[should_panic]
    fn bug_traverse() {
        struct Traverser;

        #[derive(Clone, PartialEq, Eq, Hash, Debug)]
        enum D {
            A(usize),
            B,
        }

        impl Sig for D {
            fn sig(&self) -> SigS {
                match self {
                    D::A(..) => SigS {
                        val_outs: 1,
                        ..SigS::default()
                    },
                    D::B => SigS {
                        val_ins: 2,
                        val_outs: 1,
                        ..SigS::default()
                    },
                }
            }
        }

        impl<'g, 'h: 'g> Lower<'g, 'h, D, D> for Traverser {
            fn lower(&mut self, node: Node<'h, D>, ncx: &'g NodeCtxt<D>) -> Node<'g, D> {
                let op = match &*node.kind() {
                    NodeKind::Op(op) => op.clone(),
                    _ => unreachable!(),
                };
                match op {
                    D::A(val) => {
                        println!("D::A");
                        ncx.mk_node(D::A(10))
                    }
                    D::B => {
                        let p1 = self.lower(node.val_in(0).origin().producer(), ncx);
                        let p2 = self.lower(node.val_in(1).origin().producer(), ncx);

                        match (p1.kind().clone(), p2.kind().clone()) {
                            (NodeKind::Op(D::A(l)), NodeKind::Op(D::A(r))) => {
                                let x = ncx.mk_node(D::A(l + r));
                                println!("two D::A");
                                x
                            }
                            _ => {
                                println!("D::B");
                                ncx.node_builder(D::B)
                                    .operand(p1.val_out(0))
                                    .operand(p2.val_out(0))
                                    .finish()
                            }
                        }
                    }
                }
            }
        }

        let ncx = NodeCtxt::new();
        let a1 = ncx.mk_node(D::A(2));
        let a2 = ncx.mk_node(D::A(3));
        let b1 = ncx
            .node_builder(D::B)
            .operand(a1.val_out(0))
            .operand(a2.val_out(0))
            .finish();

        let mut trav = Traverser;
        let ncx_out = NodeCtxt::new();
        let x = trav.lower(b1, &ncx_out);
    }

    #[test]
    fn unreachable_code_elimination() {
        let hir = NodeCtxt::new();

        let n_sub = hir
            .node_builder(Hir::Sub)
            .operand(hir.mk_node(Hir::I32(2)).val_out(0))
            .operand(hir.mk_node(Hir::I32(5)).val_out(0))
            .finish();

        let n_add = hir
            .node_builder(Hir::Add)
            .operand(n_sub.val_out(0))
            .operand(hir.mk_node(Hir::I32(8)).val_out(0))
            .finish();

        let n_mul = hir
            .node_builder(Hir::Mul)
            .operand(hir.mk_node(Hir::I32(2)).val_out(0))
            .operand(hir.mk_node(Hir::I32(5)).val_out(0))
            .finish();

        hir.print(&mut io::stdout().lock()).unwrap();

        let mut hir_to_lir = HirToLir::new();
        let lir = NodeCtxt::new();
        let lir_add = hir_to_lir.lower(n_add, &lir);
        lir.print(&mut io::stdout().lock()).unwrap();
    }
}
