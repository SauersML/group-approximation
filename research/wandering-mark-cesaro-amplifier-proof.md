---
rg: 2
id: wandering-mark-cesaro-amplifier-proof
kind: route
title: Compare canonical Cesaro growth with the finite-matrix Dirichlet ceiling
target: wandering-mark-cesaro-amplifier
requires: []
---

Assume `(WCA2)--(WCA3)` and choose one integer `t>B/a`.  The element
`p Sigma_t` has finite rational support, so its squared `2`-norm is a finite
linear combination of canonical trace values of group words.  If `Gamma`
were hyperlinear, a canonical microstate sequence would therefore satisfy

```text
||p(U_n) Sigma_t(U_n)||_2^2
   -> ||p Sigma_t||_(2,tau_Gamma)^2 >= at > B.
```

But its presentation defect tends to zero, and `(WCA3)` bounds the same
quantity by `B+omega_t(Def_R(U_n))->B`, a contradiction.  This proves the
main assertion.

For the stated Dirichlet certificate, diagonalize a unitary `W`.  At a
spectral value `exp(i theta)`,

```text
(1-cos(theta)) |sum_(k=0)^(t-1) exp(ik theta)|^2
 = 2 sin^2(t theta/2) <= 2.
```

Functional calculus gives
`Sigma_t^*(1-Re W)Sigma_t<=2I`.  Hence `(WCA4)` implies `(WCA3)` with
`B=2C` (and the same defect modulus).

Finally let `P=(1-d)/2`.  If the `2t` elements `w^k,dw^k`, `0<=k<t`, are
pairwise distinct, they are an orthonormal family in
`L^2(L(Gamma),tau_Gamma)`.  Expanding

```text
P Sigma_t = (1/2) sum_(k<t) (w^k-dw^k)
```

therefore gives `||P Sigma_t||_2^2=(1/4)(2t)=t/2`.  Thus `(WCA2)` holds
with `a=1/2`, proving the final specialization as well.
