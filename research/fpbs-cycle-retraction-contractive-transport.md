---
rg: 2
id: fpbs-cycle-retraction-contractive-transport
kind: claim
title: Polar transport preserves positive cycle contractions and gives an exact iterative cost identity
distinct_from:
  fpbs-relative-cycle-retraction-rounding: that bounds cost using R K R-star, which need not be a positive contraction; this transports the compressed operator by a polar unitary and preserves the hypotheses needed for iteration
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-iteration.md
---

Let R be a bounded equivariant path retraction from a bounded-degree
generating graphing H onto J, and W=ker R. For 0<=K<=I there is a
positive contraction K' on the J-edge module such that

    Tr(K')=Tr(K)-Tr(P_W K)<=Tr(R K R^*),
    c(J)=c(H)-Tr(K)+Tr(K')-Tr(P_W(I-K)).

If 0<=K<=P_Z(H), choose the polar unitary of R restricted to
Z(H) intersect W-perp; then 0<=K'<=P_Z(J). This version can be
iterated through connected retained graphings, with nonincreasing
trace and the telescoping cost identity in Section 3 of the artifact.
No decay to zero is asserted. Section 4 tests the iteration against
the previously known independent-priority cost obstruction.

The result is a written deduction from standard finite-trace
operator theory, not a novelty claim or universal Fixed Price proof.
