---
rg: 2
id: tree-action-with-elliptic-stabilizers-kills-lattice-transfer
kind: claim
title: A tree action with locally elliptic vertex stabilizers forces rational L2-Betti numbers on the complex
distinct_from:
  tree-by-elliptic-lattices-satisfy-strong-atiyah: that treats discrete subgroups of a product of an elliptic-by-abelian group with a tree group; this treats any group of automorphisms acting on a tree with locally elliptic vertex stabilizers, needs no product structure, and draws the transfer conclusion on the complex.
  complex-with-irrational-and-torsion-free-lattices: that is the open existence question for the lattice transfer; this kills it on every complex where the torsion-free group lies in such a tree action.
artifacts:
  - research/artifacts/atiyah-lattice-complex-2026-09-12.md
---

**ESTABLISHED** by [[elliptic-stabilizer-tree-transfer-obstruction-proof]].

**Setting.**
- `X` is a connected locally finite simplicial complex.
- `Γ ≤ Aut(X)` is discrete and torsion-free, and acts freely on simplices and cocompactly.
- `H` is a subgroup with `Γ ≤ H ≤ Aut(X)`, acting on a locally finite tree `T`. No
  continuity is assumed.
- Every vertex stabilizer `H_v` is locally elliptic in `Aut(X)`: every finite subset of
  `H_v` lies in a compact subgroup of `Aut(X)`.

**Conclusion.**
1. `Γ` acts on `T` freely and without inversions.
2. `Γ` embeds as a discrete torsion-free subgroup of `Aut(T)`.
3. `Γ` satisfies Strong Atiyah over every subfield `K ⊆ C` closed under complex conjugation.

**Consequence.** Every discrete `G ≤ Aut(X)` that acts freely on simplices and cocompactly
has `b_k^(2)(X;G) ∈ Q` for all `k`. So `X` cannot witness
`complex-with-irrational-and-torsion-free-lattices`.

**Remark, not part of the claim.** The intended instances are elliptic-by-tree automorphism
groups: `N ◁ H` closed and locally elliptic, with `H/N` acting on `T` with compact
stabilizers. There `H_v` is locally elliptic provided local ellipticity is closed under
extensions of locally compact groups (Platonov). That closure theorem was not verified from
a source in this lane. The candidate complexes are Cayley complexes of the free lamplighters
`Z/p ≀ F_n`, through the lamp-forgetting map to the tree of `F_n`; this is unchecked.
