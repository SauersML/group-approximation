---
rg: 2
id: bernoulli-center-boundary-interference-proof
kind: route
title: Compute the independent one-site coupling and compose it with its inverse
target: bernoulli-center-measurement-retains-boundary-interference
requires:
  - two-site-a5-plancherel-center-separates-mark
---

Canonical trace on distinct lamp coordinates is the product of their
regular traces.  Since `g^(-1)p!=p`, for `i,j in {0,1}` one has

```text
tau(P_i u_g P_j u_g^*)=tau(P_i P_j^(g^(-1)p))=mu_i mu_j.
```

This proves `(BCI1)`, and the same calculation applies to the inverse.  The
independent coupling is idempotent for the composition `(FPC2)`, proving
`(BCI2)`.  The four absolute entry differences from `Diag(mu)` are all
`q(1-q)`, so total variation is `2q(1-q)`.  Substituting `q=5/12` gives
`35/72`.

