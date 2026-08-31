---
rg: 2
id: stw22-uniform-corner-bundles-have-uniform-traces
kind: claim
title: Uniform corner contractibility forces trace continuity over every finite-dimensional base
distinct_from:
  stw22-dim2-factor-bundles-have-uniform-traces: that theorem obtains the required loop modulus automatically for all separable finite-factor fibres and stops in dimension two; the present theorem reaches arbitrary finite dimension under an explicit higher corner-connectivity datum.
  stw22-full-fundamental-group-trivial-bundles-finite-dimensional: that theorem treats one trivial fixed-fibre bundle; the present theorem permits nontrivial bundles and varying fibres.
  stw22-locally-trivial-finite-dimensional-bundles: that theorem treats locally trivial hyperfinite bundles chartwise; the present theorem includes locally trivial bundles with any fixed full-fundamental-group fibre and does not require a global or local algebra trivialization once the intrinsic L2 module is countably generated.
artifacts:
  - research/artifacts/stw22-uniform-corner-bundle-selection-audit-2026-08-30.md
---

Let `(M,E)` be a factorial tracially complete C-star algebra over a compact
Hausdorff space `K` of finite covering dimension `d`.  Suppose its intrinsic
Hilbert `C(K)`-module is countably generated, and suppose every fibre `M_x`
is a `II_1` factor.  Thus every fibre has separable predual.

Assume the following uniform corner condition through degree `d-1`.
For every `epsilon>0` there is `delta>0` such that, simultaneously for
every `x in K`, every projection `r in M_x`, and every
`0<=j<=d-1`, each continuous map

```text
S^j -> U(rM_xr)
```

whose image lies in a `delta`-ball about one point extends over
`B^(j+1)` inside the concentric `epsilon`-ball.  Here all norms are the
ambient fibre `2`-norm.  For `d=0` this condition is empty.

Then every bounded positive trace on every norm/`2`-norm fibre gap
vanishes.  Consequently every tracial state on `M` is uniquely

```text
a |-> integral_K E(a)(x) dmu(x)
```

for a Radon probability measure `mu`, and is continuous for the uniform
`2`-norm.

In particular the conclusion holds if every fibre is isomorphic to one
fixed separable-predual `II_1` factor `N` with full fundamental group.
No local triviality is needed for this corollary beyond the stated
countable generation.  Hence it applies, a fortiori, to every locally
trivial tracial W-star bundle with fixed full-fundamental-group fibre `N`
over a finite-dimensional compact Hausdorff base.  This includes locally
trivial bundles with a fixed McDuff fibre.
