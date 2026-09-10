---
rg: 2
id: fpbs-cycle-retraction-contractive-transport
kind: claim
title: Cycle augmentation and polar transport give fully charged connected exchanges
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

If H already generates the full relation, adding new orbit edges A
of cost a gives H^+=H union A and a cycle projection difference
Q=P_Z(H^+)-P_Z(H) of trace a. For cycle-supported K, the augmented
K^+=K+Q is a positive contraction with Tr(K^+)=Tr(K)+a. Thus
c(H^+)-Tr(K^+)=c(H)-Tr(K), and additions may be alternated with
the connected deletions above. Section 5 proves the resulting exact
cost identity. Across a whole add-then-delete step the trace can
increase; no uncharged addition or general decay claim is made.

The same-relation hypothesis is essential. Section 6 checks it
against sparse reconnection of the free minimal spanning forest,
whose subrelation has a different first Betti number.

The result is a written deduction from standard finite-trace
operator theory, not a novelty claim or universal Fixed Price proof.
