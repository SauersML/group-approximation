---
rg: 2
id: cyclotomic-class-group-counts-zp-actions-on-stable-o2
kind: claim
title: The ideal class group of Q(zeta_p) counts the bootstrap Z_p-actions on stable O_2 with one fixed crossed product
distinct_from:
  bootstrap-zp-actions-realize-every-cyclotomic-k-module: that proves the complete equivariant K-invariant of an action with contractible restriction is one arbitrary cyclotomic module; this counts actions up to cocycle conjugacy through that module and isolates the rank-one layer, where the class group appears.
---

**ESTABLISHED (derivation from Köhler's UCT, Meyer's realization theorem as
quoted by Meyer--Nadareishvili, and the Gabe--Szabó dynamical
Kirchberg--Phillips theorem).**  Let `p` be prime, `G = Z/p`,
`O = Z[ζ_p, 1/p]`, and `h_p` the class number of `Q(ζ_p)`.

1. The map `α ↦ K_*((O_2 ⊗ K) ⋊_α G)`, with the dual action as `ζ_p`, is a
   bijection between two sets:
   - pointwise outer actions `α : G ↷ O_2 ⊗ K` in the equivariant bootstrap
     class, up to cocycle conjugacy;
   - countable Z/2-graded `O`-modules, up to isomorphism.
2. Restrict to modules with `K_1 = 0` and `K_0` finitely generated,
   torsion-free, of rank one.  These are the invertible fractional ideals of
   `O`, and `Cl(O) = Cl(Q(ζ_p))`.  So there are exactly `h_p` such actions up to
   cocycle conjugacy.
3. All `h_p` crossed products are isomorphic to one C\*-algebra: the stable UCT
   Kirchberg algebra with `K_0 ≅ Z[1/p]^(p−1)` and `K_1 = 0`.  The dual actions
   are pairwise not KK^Ĝ-equivalent.

`h_p = 1` exactly for `p ≤ 19` (Masley--Montgomery, J. reine angew. Math.
286/287 (1976)).  `h_23 = 3`, so
there are three cocycle-conjugacy classes of such `Z/23`-actions on `O_2 ⊗ K`
with the same crossed product, told apart by the ideal classes of `Q(ζ_23)`.
The class-number values were not re-read from source.

**Why it matters here.**  It is the positive face of the fence in
`bootstrap-zp-actions-realize-every-cyclotomic-k-module`.  Over contractible
algebras the whole K-theoretic world is cyclotomic arithmetic, including Kummer's
class groups.  A UCT witness is whatever arithmetic does not see.

No priority is claimed.  The `O`-module normal form is Meyer--Nadareishvili
Proposition 5.1.  A text search of arXiv:2604.12529 and arXiv:2205.04933 found
no mention of class groups.  Izumi's and Meyer's earlier papers were not
searched.

Proof: `cyclotomic-class-group-counts-zp-actions-on-stable-o2-proof`.
