---
rg: 2
id: complex-with-irrational-and-torsion-free-lattices
kind: claim
title: Some complex carries free cocompact actions of a group with an irrational L2-Betti number and of a torsion-free group
distinct_from:
  algebraic-strong-atiyah-counterexample-exists: that asks for a torsion-free group and a matrix with non-integral kernel dimension; this asks for a geometric object, one complex shared by an irrational-valued group and a torsion-free group, which produces such a matrix through proportionality.
  free-cocompact-lattices-proportional-l2-betti: that is the established proportionality theorem; this is the open existence question the transfer needs.
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

**OPEN.** There is a connected locally finite simplicial complex `X` with discrete
`G, Γ ≤ Aut(X)`, both acting freely on simplices and cocompactly, such that `Γ` is
torsion-free and `b_k^(2)(X;G)` is irrational for some `k`.

With `free-cocompact-lattices-proportional-l2-betti`, this gives
`algebraic-strong-atiyah-counterexample-exists`: the Laplacian `Δ_k` over `Z[Γ]` has
kernel dimension `r·b_k^(2)(X;G)`, which is irrational.

## What a witness must satisfy

- **`G` is not virtually torsion-free.** A torsion-free finite-index `G' ≤ G` has
  `b_k^(2)(X;G') = [G:G'] b_k^(2)(X;G)`, already a counterexample, so the transfer
  would be idle. The published irrational groups (lamplighter constructions of
  Grigorchuk–Żuk, Dicks–Schick, Austin, Grabowski, Pichot–Schick–Żuk) have finite
  subgroups of unbounded order.
- **`Aut(X)` is non-discrete.** If it were discrete, `G` and `Γ` would have finite
  index in it, so `G ∩ Γ` would be torsion-free of finite index in `G`.
- **`X` is not contractible.** A free cellular action on a finite-dimensional
  contractible complex forces finite cohomological dimension, hence torsion-freeness.
  In particular `X` is not CAT(0).
- **`Γ` lies outside every class where Strong Atiyah is proved**, and `Γ`, `G` are
  uniform lattices in `Aut(X)`, hence quasi-isometric.

## Attempts

* **Discrete automorphism group.** *Dead*: the finite-index intersection reduces to
  the original problem for `G`, as above.
* **CAT(0) or contractible `X`.** *Dead*: free actions of groups with torsion are
  impossible there.
* **Horocyclic products and tree products** (Diestel–Leader-type `X`, where lamplighters
  are uniform lattices). *Dead for every `X` whose automorphism group embeds closed in
  `H_1 × H_2`, with `H_1` locally-elliptic-by-(torsion-free abelian) and `H_2` a closed
  tree group.* By `tree-by-elliptic-lattices-satisfy-strong-atiyah`, torsion-free
  lattices there satisfy Strong Atiyah, so the contrapositive of proportionality forces
  rational values. Whether `Aut(DL(n,n))` has this form was not checked from source.
* **Symmetrize a known irrational matrix.** *Deferred, no attack run.* Realize a
  lamplighter matrix with irrational kernel dimension as a cellular Laplacian of a free
  cocompact complex whose automorphism group is non-discrete, outside the class above,
  and contains a torsion-free uniform lattice. Candidate ambient groups are those with
  irreducible torsion-free lattices outside class `C` (Burger–Mozes-type square
  complexes). No such complex is known to carry an irrational L²-Betti number, and the
  non-contractibility requirement rules out the square complexes themselves.
