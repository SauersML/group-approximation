---
rg: 2
id: hilbert-embeddable-witness-impossible-proof
kind: route
title: Contrapose the necessary-condition route through the refuted approximation
target: hilbert-embeddable-witness-impossible
requires: [two-point-approximation-fails]
---

# Contrapose the necessary-condition route through the refuted approximation

The route `witness-yields-two-point-approximation` establishes the
implication: a Hilbert embeddable weak-soficity witness for the wreath
yields two-point approximation data at the marked pair `(Γ, hΓ)` for every
window and precision (its body carries the Clifford-theory computation;
its validity is exactly what a route's existence asserts).
`two-point-approximation-fails` establishes that no such data exists.
Hence no such witness exists, and by the identification recorded in
`hilbert-embeddable-is-representation-realized`, `W ∉ 𝒞_FU`.

The invalidations this claim carries kill precisely the two routes into
`hyperlinear-nonsofic-group` whose prerequisite was the witness claim.
The third consumer, `witness-yields-two-point-approximation` itself, is
deliberately NOT invalidated: it is a valid implication — this very proof
consumes its validity — and it simply becomes forever-blocked on a refuted
prerequisite, which is the correct permanent record of why the lane
closed.
