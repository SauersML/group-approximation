---
rg: 2
id: two-packet-linear-trace-proof
kind: route
title: Classify the finite involution fibers and separate them by image versus kernel
target: two-packet-linear-trace-vanishes
requires: []
artifacts:
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
  - research/artifacts/check_linear_identity_invariant.py
  - research/artifacts/verify-kl-gate-c3-corner.py
---

## Direct proof

An identity monomial in `AP_x` forces a conjugate of a nontrivial constant
transposition into `supp(e)supp(A)^(-1)supp(e)`; for `P_xB` the same argument
uses `supp(e)supp(B)^(-1)supp(e)`.  The exact finite normal-form certificate
classifies the involutions in the first set as `1` and

```text
I+[[0,t_i],[0,0]],   I+[[0,0],[t_i,0]],
I+t_i[[1,1],[1,1]]                         (i=0,1),
```

and in the second set by replacing `t_i` with `s_i`.

If `sigma` is a nontrivial constant transposition, `N=sigma-I` is square-zero
on the right `R`-module `R^2` and `im(N)=ker(N)`.  Conjugation preserves this
equality.  For `a=t_i`, `aR=R` but `rAnn(a)` contains `s_(1-i)`.  For `a=s_i`,
`rAnn(a)=0` but `aR!=R`.  Substitution in each of the upper, lower, and
symmetric matrices above gives `im(N)` properly contained in `ker(N)`.
Neither the identity nor any listed nonidentity involution can therefore be a
conjugate of `sigma`.  No identity monomial occurs, proving both trace
equalities.
