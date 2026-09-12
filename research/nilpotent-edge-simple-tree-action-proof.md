---
rg: 2
id: nilpotent-edge-simple-tree-action-proof
kind: route
title: Minimize Hirsch length over infinite subtree fixators and read the minimizer in its abstract commensurator
target: nilpotent-edge-simple-tree-action-has-finite-fixator
requires: []
---

**Standard inputs.**

- (P1) Subgroups of finitely generated virtually nilpotent groups are finitely
  generated and virtually polycyclic.  The Hirsch length satisfies
  `h(H) <= h(K)` for `H <= K`, with equality if and only if `[K:H]` is finite,
  and `h(K) = 0` if and only if `K` is finite (Segal, *Polycyclic Groups*,
  Chapter 1).
- (P2) A finitely generated virtually nilpotent group `Q` has a finite-index
  torsion-free nilpotent subgroup `Q'`.  An isomorphism between finite-index
  subgroups of `Q'` extends uniquely to an automorphism of the rational
  Mal'cev completion.  The Lie algebra `n` of that completion has dimension
  `h(Q)`.  This gives an injective homomorphism
  `Comm(Q) = Comm(Q') -> Aut(n) <= GL_h(Q)(Q)`, where `Q` inside the brackets is
  the rational field.
- (P3) Finitely generated linear groups are residually finite (Mal'cev).
- (P4) A tree automorphism fixing two vertices fixes the geodesic between them
  pointwise.

**Proof.**  By (P4), a finite subtree `F` containing an edge has pointwise
fixator `Fix(F)` inside an edge stabilizer, so by (P1) it has a Hirsch length.
Suppose every such `Fix(F)` is infinite.  Choose `F` with `m = h(Fix(F))`
minimal and put `Q = Fix(F)`.  Then `m >= 1`.

*Commensuration.*  For `s in S`, (P4) gives
`Q cap sQs^-1 = Fix(F) cap Fix(sF) = Fix(F')`, where `F'` is the convex hull of
`F cup sF`, a finite subtree containing an edge.  By assumption `Fix(F')` is
infinite, so minimality gives `h(Fix(F')) >= m`.  It is a subgroup of `Q` and of
`sQs^-1`, both of Hirsch length `m`, so by (P1) it has finite index in each.
So `S` commensurates `Q`, and conjugation is a homomorphism `c : S -> Comm(Q)`.

*Kernel.*  `ker c` is normal in the simple group `S`.

- `ker c = S`.  Let `s_1, ..., s_k` generate `S`.  Each `c(s_i)` is trivial,
  so `s_i` agrees with the identity on, that is centralizes, a finite-index
  subgroup `Q_i` of `Q`.  Then `Q_0 = Q_1 cap ... cap Q_k` has finite index in
  `Q`, so it is infinite, and it is centralized by every generator, so
  `Q_0 <= Z(S)`.  An infinite simple group is nonabelian, so `Z(S) = 1`.  This
  is a contradiction.
- `ker c = 1`.  By (P2), `S` embeds in `GL_m` of the rationals.  By (P3), the
  finitely generated group `S` is residually finite.  An infinite simple group
  has no nontrivial finite quotient, so it is not residually finite.  This is a
  contradiction.

So some `Fix(F)` is finite.  If `S` has no global fixed point, apply the
argument to the minimal invariant subtree.  It contains an edge, and its edge
stabilizers are subgroups of edge stabilizers of `T`, so (P1) still applies.

**Where a pairwise version stalls.**  Minimize only over segments `sigma`.
Then `Q cap sQs^-1` is the fixator of the hull of `sigma cup s sigma`, which
need not be a segment, so minimality gives no lower bound on its Hirsch length.
Every `s` for which `sigma cup s sigma` lies on one geodesic does commensurate
`Fix(sigma)`, since that geodesic segment is a larger segment whose fixator
has Hirsch length at least the minimum.  These elements are not known to
generate `S`.
