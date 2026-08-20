---
rg: 2
id: hard-sign-transport-captures-exit-mass
kind: claim
title: One hard-sign conjugacy captures the whole relative Pauli exit up to relator energy
distinct_from:
  finite-group-multiplicity-mismatch-pays-hs-energy: that compares full isotypic multiplicity vectors using a finite-group spectral gap; this uses one central involution and gives the sharp leakage constant one quarter.
  free-root-first-detection-eigenvectors-localize-exactly: that identifies an already localized eigenvector with one boundary layer; this forces a transported hard child into the negative top-sign layer.
  relative-pauli-child-split-gives-one-exit-copy: that supplies the source exit projection and its mass; this proves the target first-hit projection captures it.
---

Let `A,B` be self-adjoint involutions in a tracial matrix algebra, let `U` be
unitary, and let `P` be a projection satisfying

```text
AP=PA=-P.
```

Put `R_-=(I-B)/2`.  Then

```text
tau(P)-tau(R_- U P U^*)
 = ||(I-R_-)UP||_2^2
 <= (1/4)||BU-UA||_2^2.                               (HST1)
```

Thus a source child on which one named hard commutator is negative must be
transported into the target's negative hard-sign sector.  Every unit of mass
sent to the positive sector pays four units of squared intertwining defect.
No finite-group spectral-gap constant or multiplicity classicalization is
needed.

Apply `(HST1)` after local packet exactification.  By
`fanizza-bad-atoms-have-symmetric-frames`, every forbidden atom's rank-two
escape can be aligned to the same hard form `e_02^*`; its source hard
commutator `A` is negative on the exit half from
`relative-pauli-child-split-gives-one-exit-copy`.  By
`fanizza-symmetric-kernel-has-two-root-e5-clock`, the corresponding target
word `B_n` is the degree-`2n` E5 top root on the prefix carrier.  If `r_n` is
the transported mass in `(I-B_n)/2`, then

```text
r_n >= s_n/2 - (1/4) E_hard,n - exactification drift,  (HST2)
```

where `s_n` is total forbidden packet mass at level `n`.

Finally `corner-localized-non-ce-bcs-energy-gap` gives

```text
s_n >= beta_B^corner q_n - C p(n)sqrt(E)               (HST3)
```

unless the original shared BCS relations already pay that energy on the
active corner.  Combining `(HST2)--(HST3)` yields the lower first-hit exit
bound `(BFE3)` with

```text
eta=beta_B^corner/2
```

and polynomial error.  The statement is conditional only on placing the
aligned hard-sign conjugacy in the same group presentation and using the same
prefix carrier; the normalized-HS payment itself is `(HST1)`.
