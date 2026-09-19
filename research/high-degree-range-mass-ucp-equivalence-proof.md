---
rg: 2
id: high-degree-range-mass-ucp-equivalence-proof
kind: route
title: Use Smith on subcritical blocks and take full positivity order on ucp lifts
target: high-degree-range-mass-is-exactly-tracial-ucp-liftability
requires:
  - finite-range-block-mass-upgrades-diverging-positivity-to-ucp
---

Assume condition 2.  The replacement theorem
`finite-range-block-mass-upgrades-diverging-positivity-to-ucp` supplies ucp
maps `psi_n` with

```text
||psi_n(x)-phi_n(x)||_(2,d_n) <= 2 sqrt(rho_n)
```

for every contraction `x in S`, where `rho_n` is precisely the mass in
condition 2.  Hence `(psi_n)` represents `Theta`, proving condition 1.

Conversely, assume condition 1.  Put

```text
phi_n=psi_n,                 k_n=max(n,d_n).
```

Every ucp map is `k_n`-positive.  Every concrete irreducible summand of a
unital subalgebra of `M_(d_n)` has degree at most `d_n<=k_n`.  Consequently
there are no summands with `r_(n,j)>k_n`, the supercritical mass is
identically zero, and `k_n>=n` tends to infinity.  This proves the
equivalence without any assumption on growth of the coordinate dimensions.
