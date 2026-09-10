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

The iteration also obeys a spectral restriction (Section 8). On each
cycle module put N_n(t)=Tr(1_[0,t](K_n)) for 0<=t<1. Then
N_n(t)<=N_0(t) through both charged additions and polar compressions.
If g=C(X)-1-beta_1 and kappa is the kernel dimension of K_0 on
Z(H_0), then

    Tr(K_n)>=t(g-N_0(t)),
    Tr(K_n)->0 implies g<=kappa.

Section 9 constructs genuine zero-kernel relative certificates on
countable invariant-copy extensions Y of X with C(Y)=C(X). For
finitely generated groups their generating source graphings can
be arbitrarily near C(Y). Therefore a universal trace-zero theorem
for all these initializations would imply the stronger cost--Betti
equality. No example violating that equality is asserted.

Section 10 retains the weaker sufficient stopping condition from
the exact identity: Tr(K_n)-sum_{i<n} eta_i<=delta gives
C(X)<=c(Phi)+delta. It proves no general selection achieving it.

The result is a written deduction from standard finite-trace
operator theory, not a novelty claim or universal Fixed Price proof.
