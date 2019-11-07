use crate::rvsdg::{Node, NodeCtxt, NodeKind, Sig, SigS};

trait Lower<'g, S: Sig, T: Sig> {
    fn lower(&mut self, node: Node<'_, S>, ncx: &'g NodeCtxt<T>) -> Node<'g, T>;
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

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

struct HirToLir;

impl<'g> Lower<'g, Hir, Lir> for HirToLir {
    fn lower(&mut self, node: Node<'_, Hir>, ncx: &'g NodeCtxt<Lir>) -> Node<'g, Lir> {
        let node_kind = &*node.kind();
        let op = match node_kind {
            NodeKind::Op(op) => op,
            _ => unimplemented!(),
        };
        match op {
            Hir::I32(val) => ncx.mk_node(Lir::I32(*val)),
            Hir::Usize(val) => ncx.mk_node(Lir::Usize(*val)),
            Hir::Array(elems) => {
                // Creates an allocation node for the array size, creates a store node for every
                // array element, then merge all stores' state outputs.
                let element_size_in_bytes = 4usize;
                let elem_size_node = ncx.mk_node(Lir::Usize(element_size_in_bytes));
                let array_length = ncx.mk_node(Lir::Usize(elems.len()));

                let array_size_node = ncx
                    .node_builder(Lir::Mul)
                    .operand(array_length.val_out(0))
                    .operand(elem_size_node.val_out(0))
                    .finish();

                let alloc_node = ncx
                    .node_builder(Lir::Alloc)
                    .operand(array_size_node.val_out(0))
                    .finish();

                let mut merge_node_builder = ncx.node_builder(Lir::Merge {
                    num_of_values: 1, // the array base address
                    num_of_states: elems.len(),
                });

                let addr = alloc_node.val_out(0);

                for (i, &val) in elems.iter().enumerate() {
                    let elem_byte_offset = ncx
                        .node_builder(Lir::Mul)
                        .operand(ncx.mk_node(Lir::Usize(i)).val_out(0))
                        .operand(elem_size_node.val_out(0))
                        .finish();

                    let elem_addr = ncx
                        .node_builder(Lir::Add)
                        .operand(addr)
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

                let merge_node = merge_node_builder.operand(addr).finish();

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
                    .operand(ncx.mk_node(Lir::I32(4)).val_out(0))
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
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Hir, HirToLir, Lower};
    use crate::rvsdg::{Node, NodeCtxt, NodeKind, Sig, SigS};
    use std::io;

    #[test]
    fn hir_to_lir() {
        let hir = NodeCtxt::new();

        let subscript = hir
            .node_builder(Hir::Subscript)
            .operand(hir.mk_node(Hir::I32(110)).val_out(0))
            .operand(hir.mk_node(Hir::I32(7)).val_out(0))
            .finish();

        let mut hir_buffer = Vec::new();
        hir.print(&mut hir_buffer).unwrap();
        let hir_content = String::from_utf8(hir_buffer).unwrap();

        assert_eq!(
            hir_content,
            r#"digraph rvsdg {
    node [shape=record]
    edge [arrowhead=none]
    n0 [label="{{I32(110)}|{<o0>0}}"]
    n1 [label="{{I32(7)}|{<o0>0}}"]
    n2 [label="{{<i0>0|<i1>1}|{Subscript}|{<o0>0}}"]
    n0:o0 -> n2:i0 [color=blue]
    n1:o0 -> n2:i1 [color=blue]
}
"#
        );

        let mut hir_to_lir = HirToLir;
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
    n0 [label="{{I32(110)}|{<o0>0}}"]
    n1 [label="{{I32(7)}|{<o0>0}}"]
    n2 [label="{{GlobalState}|{<o0>0}}"]
    n3 [label="{{I32(4)}|{<o0>0}}"]
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

    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

    #[test]
    fn constant_folding() {
        struct ConstFoldOpt;

        impl<'g> Lower<'g, Ir, Ir> for ConstFoldOpt {
            fn lower(&mut self, node: Node<'_, Ir>, ncx: &'g NodeCtxt<Ir>) -> Node<'g, Ir> {
                let op = match *node.kind() {
                    NodeKind::Op(op) => op,
                    _ => unimplemented!(),
                };
                match op {
                    Ir::Lit(lit) => ncx.mk_node(Ir::Lit(lit)),
                    Ir::Var(var) => ncx.mk_node(Ir::Var(var)),
                    Ir::Add => {
                        let lhs = node.val_in(0).origin().producer();
                        let rhs = node.val_in(1).origin().producer();

                        match (*lhs.kind(), *rhs.kind()) {
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
    fn array_to_stores() {
        let mut hir = NodeCtxt::new();

        let arr = hir.mk_node(Hir::Array(vec![0, 1, 2, 2, 3, 1, 3, 4]));

        let subscript = hir
            .node_builder(Hir::Subscript)
            .operand(arr.val_out(0))
            .operand(hir.mk_node(Hir::Usize(7)).val_out(0))
            .finish();

        hir.print(&mut io::stdout().lock()).unwrap();

        let mut hir_to_lir = HirToLir;

        let mut lir = NodeCtxt::new();
        let merge = hir_to_lir.lower(subscript, &lir);

        lir.print(&mut io::stdout().lock()).unwrap();
    }
}
