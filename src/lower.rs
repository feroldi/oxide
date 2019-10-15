use crate::rvsdg::{Node, NodeCtxt, NodeKind, Sig, SigS};

trait Lower<'g, S: Sig, T: Sig> {
    fn lower(&mut self, node: Node<'_, S>, ncx: &'g NodeCtxt<T>) -> Node<'g, T>;
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Hir {
    I32(i32),
    St,
    Subscript,
}

impl Sig for Hir {
    fn sig(&self) -> SigS {
        match self {
            Hir::I32(..) => SigS {
                val_outs: 1,
                ..SigS::default()
            },
            Hir::St => SigS {
                st_outs: 1,
                ..SigS::default()
            },
            Hir::Subscript => SigS {
                val_ins: 2,
                st_ins: 1,
                val_outs: 1,
                ..SigS::default()
            },
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum Lir {
    I32(i32),
    St,
    Add,
    Mul,
    Load,
}

impl Sig for Lir {
    fn sig(&self) -> SigS {
        match self {
            Lir::I32(..) => SigS {
                val_outs: 1,
                ..SigS::default()
            },
            Lir::St => SigS {
                st_outs: 1,
                ..SigS::default()
            },
            Lir::Add | Lir::Mul => SigS {
                val_ins: 2,
                val_outs: 1,
                ..SigS::default()
            },
            Lir::Load => SigS {
                val_ins: 1,
                st_ins: 1,
                val_outs: 1,
                ..SigS::default()
            },
        }
    }
}

struct HirToLir;

impl<'g> Lower<'g, Hir, Lir> for HirToLir {
    fn lower(&mut self, node: Node<'_, Hir>, ncx: &'g NodeCtxt<Lir>) -> Node<'g, Lir> {
        let op = match *node.kind() {
            NodeKind::Op(op) => op,
            _ => unimplemented!(),
        };
        match op {
            Hir::I32(val) => ncx.mk_node(Lir::I32(val)),
            Hir::St => ncx.mk_node(Lir::St),
            Hir::Subscript => {
                let base = self.lower(node.val_in(0).origin().producer(), ncx);
                let index = self.lower(node.val_in(1).origin().producer(), ncx);
                let state = self.lower(node.st_in(0).origin().producer(), ncx);

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
                    .state(state.st_out(0))
                    .finish()
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Hir, HirToLir, Lower};
    use crate::rvsdg::NodeCtxt;

    #[test]
    fn hir_to_lir() {
        let hir = NodeCtxt::new();

        let subscript = hir
            .node_builder(Hir::Subscript)
            .operand(hir.mk_node(Hir::I32(110)).val_out(0))
            .operand(hir.mk_node(Hir::I32(7)).val_out(0))
            .state(hir.mk_node(Hir::St).st_out(0))
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
    n2 [label="{{St}|{<o0>0}}"]
    n3 [label="{{<i0>0|<i1>1|<i2>2}|{Subscript}|{<o0>0}}"]
    n0:o0 -> n3:i0 [color=blue]
    n1:o0 -> n3:i1 [color=blue]
    n2:o0 -> n3:i2 [style=dashed, color=red]
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
    n2 [label="{{St}|{<o0>0}}"]
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
}
