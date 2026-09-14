---
rg: 2
id: fpbs-burnside-normal-closure-split
kind: claim
title: The normal closure of one free generator of B(m,n), m>=3, is an infinite normal subgroup with infinite Burnside quotient
distinct_from:
  fpbs-burnside-embedding-input: that imports cyclic centralizers and subgroup embeddings for large odd Burnside groups; this is an elementary structural lemma about one specific normal subgroup, deduced from relative freeness and the centralizer theorem.
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

**Lemma 3.1 of the linked note.** Let `m >= 3`, let `n >= 665` be odd, let
`G = B(m,n)` have free generators `x_1, ..., x_m`, and let `N` be the normal
closure of `x_1`. Then:
* `N` is infinite;
* `H = <x_2, ..., x_m>` is isomorphic to `B(m-1,n)`;
* `G = N semidirect H`, and `G/N` is isomorphic to `B(m-1,n)`, which is
  infinite.

**Proof outline.**
* Relative freeness in the variety of exponent `n` gives two homomorphisms:
  `theta : B(m-1,n) -> G` onto `H`, and the retraction `r : G -> B(m-1,n)`
  killing `x_1`, with `r theta = id`.
* The map induced by `theta` from `B(m-1,n)` onto `G/N` is inverted by the
  map induced by `r`, so `ker r = N` and the extension splits.
* `B(m-1,n)` contains `B(2,n)`, which is infinite (Adian).
* If `N` were finite, the kernel `C_G(N)` of the conjugation action of `G` on
  `N` would have finite index, hence would be infinite. But it lies inside
  `C_G(x_1)`, which is cyclic of order `n`.

**Use.** Every free p.m.p. action of the infinite subgroup `N` has cost at
most `c_n <= 2 - 2/n` by `fpbs-burnside-common-upper-cost`. So `B(m,n)`
satisfies the hypothesis of `fpbs-normal-subgroup-bounded-cost-fixed-price-one`
with `K = 2`, and `fpbs-quotient-split-actions-have-cost-one` applies to its
quotient-split actions.
