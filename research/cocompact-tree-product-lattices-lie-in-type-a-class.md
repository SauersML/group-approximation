---
rg: 2
id: cocompact-tree-product-lattices-lie-in-type-a-class
kind: claim
title: Every cocompact lattice in the automorphism group of a finite product of thick leafless trees lies in the type (A) class, torsion allowed
distinct_from:
  virtually-torsion-free-tree-lattices-satisfy-pbh: that needs a torsion-free subgroup of finite index and uses plain k-graphs; this allows torsion, carrying the cube stabilizers as a finite groupoid acting self-similarly (Li's Zappa--Szep case).
  product-of-trees-lattices-satisfy-permutational-boone-higman: that allows a finite kernel on X and trees with leaves or two ends; this is its faithful case on thick leafless trees.
---

**ESTABLISHED** through `tree-lattice-with-torsion-via-zappa-szep-kgraphs` (lane
proof; not independently reviewed; no priority claimed). The finiteness input is
Li's Zappa--Sz\'ep Example (III) (arXiv:2110.04505v2, `ex:ZS`, read at source).
Its condition (F) is checked in the route, using Li's definition of the bisection
category.

**Statement.** Let `T_1, ..., T_k` be locally finite, leafless trees with more
than two ends, and `Γ <= Aut(T_1 x ... x T_k)` discrete with finitely many vertex
orbits. Factors may be permuted, and `Γ` may have torsion. Then `Γ ∈ B_A`, so
every subgroup of `Γ` embeds in a finitely presented simple group.

**Scope.**
- Faithfulness on `X` is used: `Γ` must embed in the full group through its
  action on `∏ ∂T_i`. Actions with a finite kernel, and trees with leaves or
  lines as factors, are reduced to this case only up to such a kernel (see
  Attempt 8 of `product-of-trees-lattices-satisfy-permutational-boone-higman`).
- Nothing here uses residual finiteness, irreducibility, or the factor closures.

## Priority check (bh-lattices, 2026-09-18)

This check is bounded: arXiv abstract searches plus TeX reads, and no MathSciNet or
zbMATH.

**Searches.** arXiv API for "Boone-Higman" (14 hits, all read at the abstract level),
for "products of trees" together with simple groups, full groups or higher rank
graphs, and for topological full groups of higher rank graphs.

**TeX read at source** (MSI e-prints, `gq/src/bh-lattices/`, MSI `gqsrc/bh-lattices/`):
- **Bux--Llosa Isenrich--Wu, arXiv:2408.05673.** Remark `rem:burger-mozes` (TeX
  l.1039–1041): every group in `BS_(F_k)` satisfies permutational BH, "in particular"
  the Burger--Mozes groups. This covers lattices on two trees (via
  `product-of-two-trees-lattices-satisfy-permutational-boone-higman`). There is no
  statement for three or more trees. Their l.261 says the only known obstruction to
  their Theorem C is that its input must be residually finite.
- **Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882.** The remark at TeX
  l.491–492 shows that the finitely presented simple Burger--Mozes groups are highly
  transitive and MIF, hence satisfy PBH. They treat no non-simple lattices in
  products of trees.
- **Mutter--Radu--Vdovina, arXiv:2012.05561.** They build `k`-graphs from `k`-cube
  groups (simply transitive on the vertices of a product of `k` trees) and compute
  the K-theory of their C*-algebras. So the cube `k`-graph of Step 1 of
  `tree-lattice-kgraph-power-phase-proof` is known in the simply transitive case.
  Nothing there on full groups, finite presentation or Boone--Higman.
- **Li, arXiv:2110.04505v2.** No mention of lattices, trees or buildings; it is used
  here only for finiteness.

**Abstract level only.** Fournier-Facio--Kropholler--Lyman--Zaremsky,
arXiv:2506.02319, Cor. 1.6: simple Burger--Mozes `Γ` give finitely presented `ˢV_Γ`.
D. Yang, arXiv:2105.02183: topological full groups of higher rank graphs,
simplicity and URSs; no finite presentation, lattices or BH.

**Assessment.** No source found that states Boone--Higman or PBH for lattices on
three or more trees, for non-simple non-residually-finite lattices beyond
`BS_(F_2)`, or for lattices with torsion beyond two trees. What is new here:
- **Loops.** The power-and-phase step that forces Li's loop hypothesis. bh-groupoid
  found it independently for primitive 2-graphs
  (`primitive-two-graph-fp-simple-embedding-proof`).
- **Comparison.** The refinement comparison lemma after Cuntz stabilization, and the
  resulting type (A) clopen action.
- **Torsion.** The germ-groupoid treatment of torsion.

No priority is claimed pending a citation-database search.
