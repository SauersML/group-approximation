---
rg: 2
id: norm-corona-sparse-global-character-atom-proof
kind: route
title: Exactify growing finite character windows and select one negative joint eigenspace
target: norm-corona-sparse-global-character-atom
requires: []
---

Enumerate `A=<a_0,a_1,...>` and put
`A_m=<a_0,...,a_m>`.  Choose unitary lifts `U_(j,n)` of `rho(a_j)`.  For each
fixed `m`, the involution and commutation relations of the finite group `A_m`
hold asymptotically in operator norm.  Stability of the fixed finite-dimensional
algebra `C^*(A_m)` therefore gives, sufficiently far out, exact commuting
involutions

```text
V_(0,n),...,V_(m,n)
```

arbitrarily close to the corresponding lifts.  Diagonalize in `m`: at the
`n`-th selected coordinate exactify the first `n` generators with error
tending to zero.

Because `rho(a_0)!=1` and `a_0` is an involution, the negative spectral
projection of its lift remains nonzero on an infinite subsequence.  For large
selected coordinates `V_(0,n)` therefore also has a nonzero negative
eigenspace.  Choose a nonzero joint eigenspace of
`V_(0,n),...,V_(n,n)` inside it and a rank-one projection `P_n` there.

Repeated subsequence extraction makes the sign of each fixed generator
eventually constant; call it `chi(a_j)`.  Every finite sign pattern comes
from a character of `A_n`, so the limiting signs define a character of `A`
with `chi(a_0)=-1`.  Put `P_n=0` off the selected subsequence.  The class
`P=[(P_n)]` is nonzero because `||P_n||=1` infinitely often, and for each
fixed `j`,

```text
||U_(j,n)P_n-chi(a_j)P_n||_op -> 0.
```

This is `(SGA1)--(SGA2)` in the quotient.

