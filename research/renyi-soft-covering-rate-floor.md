---
rg: 2
id: renyi-soft-covering-rate-floor
kind: claim
title: A Renyi mutual-information rate gap gives an exact quantum soft-covering strong-converse exponent
distinct_from:
  paired-same-reservoir-boundary-lemma: that asks for a group-microstate same-reservoir-or-boundary theorem; this is the external information-theoretic exponent before any Leavitt or selector translation.
  mf-trace-gap-defect-ratio-models: that compares operator-norm defect with trace visibility in MF models; this compares codebook rate with sandwiched Renyi mutual information for a classical-quantum source.
---

For every classical-quantum state `rho_XE`, rate `R>=0`, and sandwiched Renyi
order `alpha>=1`, the quantum soft-covering strong-converse exponent is

```text
Gamma_sc^(alpha)(rho_XE,R)
 =max(I_alpha(X:E)_rho-R,0).                            (RSC1)
```

In particular a uniform rate gap

```text
R<=I_2(X:E)_rho-epsilon
```

gives a positive exponent at least `epsilon` for order two.  This theorem
does not itself bound a group-microstate selector: an application must first
encode addresses and multiplicity reservoirs as the classical and quantum
systems and compare the covering divergence with normalized-HS leakage.
