---
rg: 2
id: spectral-compressed-leakage-is-finite-word-moment-functional
kind: claim
title: Leakage between word-spectral cuts is a finite word-moment functional
distinct_from:
  phase-covariance-words-exactly-measure-type-transport-leakage: that bounds a sum of mismatched phase blocks by covariance defects; this explicitly Fourier-expands one compressed leakage scalar into ordinary word moments.
  finite-phase-tags-authenticate-forbidden-cuts: that asks for a matrix-only word-spectral surrogate of a nonlinear forbidden cut; this proves the exact calculation after such a surrogate is available.
---

Let `A^m=B^n=1`, let `lambda in mu_m`, `mu in mu_n`, and let

```text
C=(1/m)sum_(r=0)^(m-1) lambda^(-r)A^r,
G=(1/n)sum_(s=0)^(n-1) mu^(-s)B^s                     (SCM1)
```

be their corresponding spectral projections.  For every unitary `U`,

```text
||(1-C)UG||_2^2=tau(G)-tau(GU^*CU)                    (SCM2)
```

and hence

```text
||(1-C)UG||_2^2
 =(1/n)sum_s mu^(-s)tau(B^s)
 -(1/(mn))sum_(r,s)
   lambda^(-r)mu^(-s)tau(B^sU^*A^rU).                 (SCM3)
```

Thus compressed leakage is a finite linear functional of ordinary word
moments whenever both cuts are canonical spectral projections of finite-order
words.  This does not turn an analytic carrier such as
`P_omega<=F_cQ_omega` into a word-spectral cut, nor do relator defects alone
force the nonzero moment values in `(SCM3)`.  The formula isolates spectral
authentication, rather than subsequent leakage algebra, as the live gate.

