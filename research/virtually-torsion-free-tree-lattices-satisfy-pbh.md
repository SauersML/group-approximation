---
rg: 2
id: virtually-torsion-free-tree-lattices-satisfy-pbh
kind: claim
title: Every virtually torsion-free cocompact lattice on a finite product of thick leafless trees satisfies permutational Boone--Higman, whatever its kernels, closures or residual finiteness
distinct_from:
  product-of-trees-lattices-satisfy-permutational-boone-higman: that is the open claim for all lattices, torsion allowed; this settles every virtually torsion-free one, for any number of factors.
  product-of-two-trees-lattices-satisfy-permutational-boone-higman: that covers two trees through Bux--Llosa Isenrich--Wu graphs of groups; this covers any number of trees through boundary k-graphs, but needs a torsion-free subgroup of finite index.
  three-tree-lattices-escape-only-via-discrete-normal-subgroups: that isolates the three-tree gap; this closes the gap for virtually torsion-free lattices.
---

**ESTABLISHED** through `virtually-torsion-free-tree-lattices-pbh-via-kgraphs`
(lane proof; not independently reviewed; no priority claimed).

**Statement.** Let `T_1, ..., T_k` be locally finite leafless trees, each with more
than two ends, `X = T_1 x ... x T_k`, and let `Γ` act on `X` with finite vertex
stabilizers and finitely many vertex orbits, possibly permuting the factors.
Suppose `Γ` has a torsion-free subgroup of finite index. Then `Γ ∈ B_A`. So every
subgroup of `Γ` embeds in a finitely presented simple group.

**Covered.** Burger--Mozes and Wise lattices, Radu's lattice, and all torsion-free
lattices on three or more trees, including any non-residually-finite,
totally non-discrete ones with discrete normal subgroups in their factor
closures.

**Not covered.** Lattices with no torsion-free subgroup of finite index, if any
exist. For those the cube k-graph must carry a finite groupoid of cube
stabilizers (Li's Zappa--Sz\'ep case, condition (F)).
