---
rg: 2
id: stw22-fixed-factor-weighted-copy-uniform-s2-fillings
kind: claim
title: Weighted-copy fibres in one separable II1 factor have uniform two-sphere fillings
distinct_from:
  stw22-all-finite-factor-weighted-copy-uniform-loop-fillings: that theorem has one loop modulus uniform across every finite factor; the present theorem fills two-spheres but its modulus may depend on the fixed II1 factor.
  stw22-weighted-purification-all-sphere-fillings: that theorem is factor-uniform in every degree for the hyperfinite factor; the present theorem treats an arbitrary fixed separable II1 factor only through degree two.
  stw22-dim2-factor-bundles-have-uniform-traces: that theorem allows varying factor fibres and uses loop fillings; the present theorem supplies the next sphere degree only when the ambient factor is fixed.
artifacts:
  - research/artifacts/stw22-fixed-factor-s2-filling-audit-2026-08-30.md
---

Fix a `II_1` factor `(N,tau)` with separable predual.  For every
`epsilon>0` there is `rho_N(epsilon)>0` with the following property,
simultaneously for every `m>=1`, `gamma>0`, and positive contraction
`a in N` satisfying

```text
m tau(supp(a))<=1-gamma.
```

Every continuous map `S^2->F_(N,m)(a)` whose image lies in the
Hilbert-sum `rho_N(epsilon)`-ball about one point of the fibre extends over
`B^3` inside the concentric `epsilon`-ball.  Moreover every such weighted
fibre is `2`-connected.  Combined with the factor-uniform loop theorem, the
family of all strictly slack weighted-copy fibres in this one `N` is
uniformly equi-`LC^2`.

The modulus is independent of the projection traces, the weight, the copy
number, and the size of the positive slack.  Dependence on `N` remains: it
enters only through the local modulus at the identity of a pointed Jekel
contraction of `U(N)`.  No factor-uniform modulus for that step is asserted.
