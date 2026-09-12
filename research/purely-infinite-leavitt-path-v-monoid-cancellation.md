---
rg: 2
id: purely-infinite-leavitt-path-v-monoid-cancellation
kind: claim
title: For a purely infinite simple Leavitt path algebra of a finite graph, nonzero projectives with equal K_0 classes are isomorphic
distinct_from:
  agp-purely-infinite-simple-k1-is-unit-abelianization: that imports the identification of K_1 with the unit abelianization for purely infinite simple rings; this is the K_0 statement that the monoid of nonzero finitely generated projectives is a group, which is what turns a K_0 class into an isomorphism of modules.
  binary-leavitt-nonzero-projectives-are-free: that is the case of the one-vertex two-loop graph, where every nonzero projective is free; this is cancellation for Leavitt path algebras of other finite graphs, whose K_0 can be a nonzero finite group.
artifacts:
  - research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md
---

**OPEN (citation to import).** Let `E` be a finite graph with `L = L_K(E)` purely
infinite simple. If `P` and `Q` are nonzero finitely generated projective right
`L`-modules with `[P] = [Q]` in `K_0(L)`, then `P ≅ Q`.

**Consequence for the host lane.** If `[1_L] = 0` in `K_0(L)`:
- `L ≅ L^2` as right modules, so `L` contains a unital Leavitt family `e, f`;
- every nonzero finitely generated projective of class `0` is isomorphic to `L`.
Those are properties (P1) and the complement half of (P2) in
`research/artifacts/bh-leavitt-path-steinberg-hosts-2026-09-12.md`.

## Attempts

- **Expected sources, not yet read.**
  - Ara--Moreno--Pardo (Algebr. Represent. Theory 2007): `V(L_K(E)) ≅ M_E`, the
    graph monoid.
  - Ara--Goodearl--Pardo, arXiv:math/0111066: for a purely infinite simple ring,
    `V(R) \ {0}` is a group. The repo already imports Theorem 2.4 of that paper
    in `agp-purely-infinite-simple-k1-is-unit-abelianization`.
  - Before importing, confirm that the exact statement covers non-regular rings.
    `L_K(E)` is von Neumann regular only when `E` is acyclic.
- **Internal route (not started).** In `L_K(E)` both idempotents are equivalent to
  orthogonal sums of vertex idempotents. Theorem B's explicit partial isometries
  (cycle with an exit, incomparable loops) should give equivalences directly, but
  the bookkeeping of equal classes versus explicit equivalence is not written.
