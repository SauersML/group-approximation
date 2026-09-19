---
rg: 2
id: diagonal-tensor-powers-regular-lamp-proof
kind: route
title: Apply Fell absorption to every diagonal tensor power of the regular packet
target: diagonal-tensor-powers-do-not-amplify-regular-lamp-center
requires: []
---

Let `Q` be finite, let `lambda_Q` be its left regular representation, and
let `pi:Q->U(H_pi)` be finite-dimensional.  The unitary

```text
delta_h tensor xi |-> delta_h tensor pi(h)^(-1)xi
```

conjugates `lambda_Q tensor pi` to
`lambda_Q tensor 1_(H_pi)`.  Hence

```text
lambda_Q tensor pi ~= lambda_Q^(dim pi),
lambda_Q^(tensor t) ~= lambda_Q^(|Q|^(t-1)).
```

Amplification does not alter normalized central-isotypic ranks.  Thus the
`rho`-isotypic mass remains `dim(rho)^2/|Q|` at every diagonal tensor power.
For `Q=K^F` this is the same product Plancherel law on `Irr(K)^F`, not a
new independent draw from that law.  In particular the mass of the labels
faithful on a coordinate set `Z` remains `(1-1/|K|)^|Z|`; for `K=A5` it is
`(59/60)^|Z|`.  This proves that diagonal tensor powers do not amplify the
regular lamp packet's centre samples.
