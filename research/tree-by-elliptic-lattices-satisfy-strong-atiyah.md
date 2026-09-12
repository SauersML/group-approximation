---
rg: 2
id: tree-by-elliptic-lattices-satisfy-strong-atiyah
kind: claim
title: Torsion-free discrete subgroups of locally-elliptic-by-abelian times tree groups satisfy Strong Atiyah
distinct_from:
  atiyah-passes-to-torsion-free-elementary-amenable-extensions: that is Schick's extension step over a normal subgroup already satisfying the conjecture; this finds a locally free normal subgroup inside any torsion-free lattice of such a product and applies that step.
  complex-with-irrational-and-torsion-free-lattices: that is the open existence question for the lattice transfer; this kills it on every complex whose automorphism group embeds in such a product.
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

**ESTABLISHED** by [[tree-by-elliptic-lattices-strong-atiyah-proof]].

Let `H_1` be a totally disconnected locally compact group and `N ◁ H_1` a closed
**locally elliptic** normal subgroup: every finite subset of `N` lies in a compact
subgroup of `H_1`. Assume `H_1/N` is torsion-free abelian. Let `H_2` be a closed
subgroup of `Aut(T)` for a locally finite tree `T`, or `H_2 = 1`. Let `Γ ≤ H_1 × H_2` be
discrete and torsion-free. Then:

- `Γ^0 = Γ ∩ (N × H_2)` is normal in `Γ` and locally free, with `Γ/Γ^0` torsion-free
  abelian;
- `Γ` satisfies the Strong Atiyah Conjecture over every subfield `K ⊆ C` closed under
  complex conjugation.

## Consequence for the lattice transfer

Suppose `Aut(X)` embeds as a closed subgroup of such a product, and a torsion-free
group acts freely and cocompactly on `X`. By the contrapositive in
`free-cocompact-lattices-proportional-l2-betti`, every group acting freely and
cocompactly on `X` has rational L²-Betti numbers on `X`. So such complexes cannot
witness `complex-with-irrational-and-torsion-free-lattices`.

The intended instances are horocyclic products of trees, where the kernel of the height
homomorphism acts by end-fixing horocycle-preserving automorphisms. Whether
`Aut(DL(n,n))` has exactly this form was not checked from source.
