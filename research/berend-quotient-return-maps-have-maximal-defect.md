---
rg: 2
id: berend-quotient-return-maps-have-maximal-defect
kind: claim
title: Any Berend finite-orbit return map recovering the volume unitary has maximal multiplicativity defect
distinct_from:
  berend-integral-k-theory-and-invisible-class: that computes the class and its vanishing in quotients; this gives an exact norm obstruction for homomorphic and completely positive return maps.
  berend-finite-orbit-quotients-are-asymptotically-isometric: that controls outgoing quotient norms; this forces a maximal defect in attempted completely positive return maps.
artifacts:
  - research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md
---

Let `A` be the exact cubic Berend algebra and let `v in U_k(C(T^3))`
represent the top exterior K-class, whose image in `K_1(A)` is nonzero.
For every nonempty finite invariant `F`, set `Q_F=C(F) ⋊ Z^2` and let
`q_F:A -> Q_F` be restriction.

Every unital homomorphism `theta:Q_F -> A` has

`||theta^(k)(q_F^(k)(v))-v||=2`.

If a unital completely positive map `sigma:Q_F -> A` instead has

`||sigma^(k)(q_F^(k)(v))-v||<1`,

then some unitary `w in M_k(C(F))` satisfies

`max{||1-sigma^(k)(w)^*sigma^(k)(w)||,
      ||1-sigma^(k)(w)sigma^(k)(w)^*||}=1`.

Consequently return maps recovering this fixed witness cannot become
uniformly multiplicative on the unit ball of `M_k(Q_F)`. This is not
an obstruction to finite decomposition rank: its return maps are not
required to be uniformly multiplicative on quotient inputs.
