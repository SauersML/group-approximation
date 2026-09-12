---
rg: 2
id: bounded-conductor-width-first-exit-proof
kind: route
title: Bound shifted overlap by the largest conductor atom
target: bounded-conductor-width-pays-uniform-first-exit
requires: []
---

For a finitely supported nonnegative sequence `mu`, extended by zero, let
`M=max_j mu_j`.  The discrete variation of the sequence must rise from zero
to `M` and return from `M` to zero.  Hence

```text
sum_j |mu_j-mu_(j-1)| >=2M.                             (BCP1)
```

By the definition of total variation and the pigeonhole bound on a
probability vector supported at at most `B` points,

```text
TV(mu,S mu)
 =1/2 sum_j |mu_j-mu_(j-1)|
 >=M>=1/B.                                              (BCP2)
```

For exact semisimple representations, decompose source and target into the
same conductor-type labels.  On label `j`, a partial intertwiner can match at
most the smaller of the source and target normalized dimension masses.
Summing the Schur-support bound gives

```text
trace(source support)
 <=sum_j min(mu_j,mu_(j-1)).                            (BCP3)
```

For probability measures,

```text
sum_j min(mu_j,mu_(j-1))=1-TV(mu,S mu),                 (BCP4)
```

so `(BCP2)--(BCP4)` prove the first-exit floor.

For a profile on a coweight lattice, push it forward to the chosen integer
root-depth coordinate.  The pushforward intertwiner overlap is an upper
relaxation of the typewise overlap, and total variation cannot increase
under pushforward.  If that marginal occupies at most `B` depths, `(BCP2)`
again gives the `1/B` loss.  Tensoring every type space and transition by a
fixed four-dimensional lamp factor multiplies all unnormalized ranks by the
same number and leaves normalized source trace unchanged.
