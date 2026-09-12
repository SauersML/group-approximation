---
rg: 2
id: balanced-controlled-whitehead-return-checksum-proof
kind: route
title: Compare the controlled Reynolds ranks and expand the returned overlap
target: balanced-controlled-whitehead-return-checksum
requires:
  - controlled-fine-reflection-superrank-orientation-law
  - adjoint-reynolds-return-needs-one-overlap-moment
---

Both Reynolds operators are orthogonal projections.  Since conjugation by
`Ad(W)` is unitary on the adjoint Hilbert space, positivity and cyclicity
give

```text
Theta_W
 =tr_ad(R_G Ad(W)R_PAd(W)^*)
 <=tr_ad(R_G)=(1+mu^2)/32.
```

Also

```text
||(I-R_G)Ad(W)R_P||_(2,ad)^2
 =tr_ad(R_P)-Theta_W
 =1/16-Theta_W.
```

Combining the two identities proves `(BCW2)--(BCW3)`.  Canonical packet
trace makes `mu=o(1)` by `(CFS5)` and finite-group HS exactification, proving
`(BCW4)`.

Finally insert

```text
R_P=|P|^-1 sum_(p in P) Ad(U(p)),
R_G=|G|^-1 sum_(g in G) Ad(U(g))
```

into `(BCW1)`.  Composition multiplies the implementing unitaries and the
normalized adjoint trace satisfies

```text
tr_ad(Ad(V))=|tr(V)|^2.
```

This gives `(BCW5)` (renaming inverses inside the uniform sums if the
opposite Reynolds convention is used).  Combining `(BCW2)` with `(BCW6)`
gives `(BCW7)`.

