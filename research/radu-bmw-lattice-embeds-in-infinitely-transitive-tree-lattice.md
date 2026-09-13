---
rg: 2
id: radu-bmw-lattice-embeds-in-infinitely-transitive-tree-lattice
kind: claim
title: Radu's BMW lattice embeds in a cocompact tree-product lattice with locally infinitely transitive projection closures
distinct_from:
  radu-bmw-lattice-embeds-in-titz-witzel-kernel: that embeds the lattice in a Kazhdan building lattice; this asks for an overgroup acting on a product of trees whose projection closures are locally infinitely transitive
  burger-mozes-infinitely-transitive-tree-groups: that imports the Burger-Mozes embedding of torsion-free one-vertex complexes; this asks for the analogue for a lattice with torsion whose torsion-free subgroup has four vertex orbits
---

**OPEN.** Radu's BMW lattice `Γ_R` (`radu-bmw-lattice-embeds-in-titz-witzel-kernel`) is
isomorphic to a subgroup of a cocompact lattice `Γ <= Aut(T_p) × Aut(T_q)` whose
projection closures `H_i` are locally `∞`-transitive with `[H_i : H_i^(∞)] < ∞`.

With `radu-bmw-lattice-nonsofic` this makes `Γ` nonsofic
(`infinitely-transitive-nonsofic-lattice-from-radu-lattice`). It is the only way left to
get a mixing action from Radu's lattice, since induced actions from `Γ_R` itself are never
mixing (`radu-lattice-induced-actions-are-never-mixing`).

## Attempts

* **Burger–Mozes Theorem 6.5 does not apply as stated.** It embeds torsion-free one-vertex
  VH-T-complexes. `Γ_R` has 2-torsion. Its torsion-free subgroup `π_1(S_R)` has four vertex
  orbits on `T_3 × T_3`, and torsion-free vertex-transitive lattices need even degrees
  (Radu, arXiv:1712.01091, p. 5).
* **Local isometry into a one-vertex complex.** A locally convex immersion `S_R → X`, with
  `X` one-vertex, is `π_1`-injective. Label each oriented edge of `S_R` by itself. For a
  vertical letter `b` from `w` to `w'`, the vertical structure map of `X` must extend
  `S_R`'s bijection, from horizontal edges ending at `w` to edges starting at `w'`, to a
  bijection of all horizontal letters. Filling the remaining corners with commutator tori
  `(a, b, a^(-1), b^(-1))` sends an edge ending at `u ≠ w` to an edge starting at `u`.
  Unless `w = w'`, this collides with `S_R`'s part. So some other completion of the partial
  VH-datum is needed, and none is recorded.
* **Torsion.** Radu's Theorem V (virtually simple `(2n, 2n+1)`-groups, arXiv:1712.01091,
  p. 5) shows that the Burger–Mozes mating method has versions with torsion. No embedding
  theorem for BMW groups was found in the pages read.
