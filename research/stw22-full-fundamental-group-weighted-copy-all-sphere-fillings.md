---
rg: 2
id: stw22-full-fundamental-group-weighted-copy-all-sphere-fillings
kind: claim
title: Full-fundamental-group factors have uniform weighted-copy sphere fillings in every finite degree
distinct_from:
  stw22-weighted-purification-all-sphere-fillings: that theorem uses the nonexpansive hyperfinite contraction; the present theorem permits any fixed separable II1 factor with full fundamental group, with moduli depending on the factor and the sphere degree.
  stw22-fixed-factor-weighted-copy-uniform-s2-fillings: that theorem works for every fixed separable II1 factor but stops at two-spheres; the present theorem reaches every finite sphere degree under the additional full-fundamental-group hypothesis.
  stw22-all-finite-factor-weighted-copy-uniform-loop-fillings: that theorem gives one loop modulus across all finite factors; the present higher-degree moduli are uniform only among the corners and weighted fibres of one fixed factor.
artifacts:
  - research/artifacts/stw22-full-fundamental-group-all-degree-audit-2026-08-30.md
---

Let `(N,tau)` be a `II_1` factor with separable predual and full
fundamental group.  Thus every nonzero corner `rNr`, with its normalized
trace, is isomorphic to `N`.  Fix `k>=0` and `epsilon>0`.  There is
`rho_(N,k)(epsilon)>0` such that, simultaneously for every `m>=1`,
`gamma>0`, and positive contraction `a in N` satisfying

```text
m tau(supp(a))<=1-gamma,
```

every continuous map `S^k->F_(N,m)(a)` contained in the Hilbert-sum
`rho_(N,k)(epsilon)`-ball about a point of the fibre extends over
`B^(k+1)` inside the concentric `epsilon`-ball.  Every such fibre is
`k`-connected for every finite `k`.

The modulus is independent of `m,a,gamma` and all projection traces, but it
may depend on `N,k,epsilon`.  In particular the theorem is not a modulus
uniform over all `II_1` factors.  The same conclusion holds under the
formally weaker hypothesis that the normalized unitary groups of all
nonzero corners of `N` admit one pointed local contraction modulus in every
finite sphere degree.
