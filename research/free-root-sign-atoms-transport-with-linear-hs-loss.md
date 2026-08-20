---
rg: 2
id: free-root-sign-atoms-transport-with-linear-hs-loss
kind: claim
title: A finite free-root character atom transports with linear, not exponential, HS loss
distinct_from:
  robust-rank-one-endpoint-marginal-floor: that starts from three measures and charges marginal drift; this constructs those measures from common spectral atoms and bounds the drift directly by root-word covariance errors.
  free-root-first-detection-eigenvectors-localize-exactly: that places an exact eigenvector in a valuation boundary; this controls approximate transport of the entire finite-stage character projection.
  finite-group-multiplicity-mismatch-pays-hs-energy: that uses a spectral gap after two finite-group representations have been chosen; this transports the common character carrier on which those representations are compared.
---

Let `A_0,...,A_m` and `B_0,...,B_m` be commuting self-adjoint involutions in
a tracial matrix algebra, let `U` be unitary, and fix signs
`epsilon_i in {+1,-1}`.  Put

```text
P=product_(i=0)^m (I+epsilon_i A_i)/2,
Q=product_(i=0)^m (I+epsilon_i B_i)/2.                 (SAT1)
```

Then

```text
||U P U^*-Q||_2
 <= (1/2) sum_(i=0)^m ||U A_i U^*-B_i||_2.             (SAT2)
```

In particular,

```text
|tau(P)-tau(Q)| <= (1/2) sum_i ||U A_i U^*-B_i||_2.    (SAT3)
```

Thus transporting one atom of an elementary abelian root stage costs only
linearly many generator covariance errors; there is no factor equal to the
number `2^(m+1)` of characters.

Moreover, suppose three context unitaries use endpoint atoms
`P_X0,P_X1,P_Y0,P_Y1`, with contexts `(X0,Y0),(X0,Y1),(X1,Y1)`.  Define each
joint block-mass law by normalized squared Hilbert--Schmidt norms of the four
blocks of its unitary.  Summing over the second label gives the trace of the
source endpoint atom, and summing over the first gives the trace of the target
endpoint atom.  Hence the first two contexts have the same left marginal and
the last two have the same right marginal, up to exactly the atom drift in
`(SAT2)` when endpoints are only approximately covariant.

For the valuation-`r` E5 detector there are `r+1` root signs, and every
required root word has length `O(r^2)`.  Telescoping its derivation from a
fixed presentation therefore gives a polynomial carrier drift.  Combined
with the robust rank-one endpoint floor, baseline carrier persistence and
no-signaling endpoint sharing do not require a common classical decoder.
