---
rg: 2
id: cook-levin-rank-pressure-needs-common-reservoir-decoder
kind: claim
title: Gatewise Cook--Levin rank pressure reaches the rational branch-capacity endpoint only after common-reservoir decoding
distinct_from:
  gatewise-cook-levin-rank-is-baseline-plus-unsat: that proves the exact sectorwise rank and multiplicity identities; this records the additional operator occurrence hypotheses needed before those multiplicities become one finite branch-capacity inequality.
  bounded-template-average-blr-occurrence-decoder: that is an open same-Hilbert occurrence decoder for a simplex table; this isolates the weaker resource-register consequence needed by the gatewise rank backend and does not claim that the decoder exists.
---

The exact identity

```text
rank R_C = m+UNSAT_C
```

does not by itself yield an MF or hyperlinearity obstruction.  To feed it to a
finite branch-capacity argument, one must additionally decode the relevant
gate occurrences onto common carrier projections `P_1,...,P_r` and turn every
rank-generated copy into partial isometries whose source projections are the
prescribed `P_i`, whose target ranges are orthogonal at each `P_j`, and whose
off-target leakage is controlled by the original relation defect.

Conditionally, suppose those objects have been decoded and let `A[j][i]` count
the authenticated branches from `P_i` to `P_j`.  With

```text
x_j=tau(P_j),
e_j=sum_(i,h)||(1-P_j)T_(j,i,h)||_2^2,
```

the existing Gram/capacity calculation gives

```text
x >= A x-e.                                                     (CLP1)
```

If an exact rational certificate satisfies

```text
A^T y >= (1+kappa)y,
```

then

```text
kappa (y.x) <= y.e.                                            (CLP2)
```

by `rational-supercritical-branch-certificate`.  Thus, if marked survival
gives `y.x>=c>0` and the missing decoder gives bounds
`e_j<=C_j Def(U)`, then

```text
Def(U) >= kappa c / sum_j(y_j C_j).                             (CLP3)
```

For a strongly connected finite automaton with one genuine branch, the
rational pair `(y,kappa)` exists by
`strongly-connected-branching-gives-rational-pressure`.

The load-bearing hypothesis is the first paragraph: the copies counted by
`2^UNSAT_C` must be authenticated on the same finite multiplicity/resource
register.  Separate contextwise Clifford packets, a classical PCP gap, or the
rank identity alone do not supply that identification.  A
dimension-independent normalized-HS operator-LTC/same-reservoir decoder
remains open.
