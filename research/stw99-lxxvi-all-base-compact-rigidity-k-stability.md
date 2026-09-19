---
rg: 2
id: stw99-lxxvi-all-base-compact-rigidity-k-stability
kind: claim
title: All compact-base projection regularity for a simple pure fiber is equivalent to K-stability of every projection corner
artifacts:
  - research/artifacts/stw99-lxxvi-all-base-compact-k-stability-audit-2026-09-05.md
---

Let `D` be a separable simple stably finite pure C*-algebra. The following
conditions are equivalent.

1. For every nonzero projection `p in D tensor K`, the canonical maps
   `pi_k(U(p(D tensor K)p)) -> K_(k+1)(p(D tensor K)p)` are isomorphisms
   for all `k>=0` (with the usual two-periodic indexing).
2. The first-factor map is an isomorphism on `V(C(S^d,D))` for every
   sphere `S^d`, `d>=1`.
3. The first-factor map is an isomorphism on `V(C(X,D))` for every
   compact metrizable space `X`, without any bound on its dimension.

In condition 1, requiring this for every projection corner includes all
matrix amplifications of each corner, so it says that all these unital
corners are K-stable. This condition is stronger than K-stability of `D`
alone if `D` is not itself unital; K-stability is not Morita invariant.

If `D` has real rank zero, these equivalent conditions hold by Zhang's
published theorem. Thus for every compact metrizable `X`, the actual
first-factor map preserves and reflects all compact Cu classes of
`C(X,D)` and all order relations between them. No nuclearity or
Z-stability of `D` is assumed.

A failure of stabilization in one corner produces an explicit sphere
witness to failure of first-factor Cu regularity: noninjectivity collapses
two projection classes, while nonsurjectivity omits a projection class.
The corresponding sphere algebra is pure by Seth--Vilalta. Consequently
an affirmative answer to STW LXXVI would imply the K-stability assertion
of STW LVIII for every unital separable simple pure algebra.

This does not identify the noncompact Cu classes over higher-dimensional
bases. Nor does it assert the unproved K-stability condition for arbitrary
simple pure coefficients. If `D` is stably projectionless, the compact
statement is vacuous.

ROUTES

stw99-lxxvi-all-base-compact-k-stability-proof
