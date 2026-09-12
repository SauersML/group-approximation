---
rg: 2
id: regular-quotient-restriction-lattice-proof
kind: route
title: Subtract the regular packet and test conjugacy fusion in the BS subgroup
target: regular-quotient-padding-repairs-exactly-the-restriction-lattice
requires: []
---

If `rho` is a genuine `Q`-representation satisfying `(RQP2)`, then in the
Grothendieck group

```text
[beta]=res([rho]-t[lambda_Q]),
```

which proves necessity.  Conversely take an integral virtual preimage

```text
z=sum_alpha n_alpha alpha.
```

For all sufficiently large `t`, every
`n_alpha+t dim(alpha)` is nonnegative.  Hence `z+t lambda_Q` is genuine and
has restriction `(RQP2)`.  A `Z`-linear section of the surjection onto the
free abelian image lattice gives the fixed-`Q` linear bound.

For `(RQP3)`, Mackey theory gives

```text
chi_beta(u(x))=sum_(h in H) psi(hx).
```

Conjugation by a diagonal element whose square is `2` replaces this with
the Fourier sum over `2H`.  Equality for every `x` would make the Fourier
transforms of the two indicator functions equal, forcing `H=2H`, contrary
to `2 notin H`.  This violates the conjugacy invariance inherited by every
restricted `Q`-character.

