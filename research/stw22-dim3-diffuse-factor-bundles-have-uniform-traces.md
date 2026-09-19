---
rg: 2
id: stw22-dim3-diffuse-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated bundles of diffuse II1 factors have only uniform traces through dimension three
distinct_from:
  stw22-dim2-factor-bundles-have-uniform-traces: that theorem permits arbitrary finite-factor fibres but stops at covering dimension two; the present theorem reaches dimension three under the diffuse-II1 fibre hypothesis.
  stw22-dim3-trivial-factor-bundles-have-uniform-traces: that theorem fixes one common factor and uses a factor-dependent pointed contraction; the present theorem permits nontrivial bundles and varying diffuse factors by a factor-uniform modulus.
  stw22-finite-dimensional-trivial-field-traces: that theorem is all finite-dimensional but hyperfinite and trivial; neither assumption is made here.
artifacts:
  - research/artifacts/stw22-dim3-diffuse-bundle-breakthrough-2026-08-30.md
---

Let `K` be compact Hausdorff with covering dimension at most three, and
let `(M,E)` be a factorial tracially complete C-star algebra over `K`.
Assume:

```text
(i)  the Hilbert C(K)-module completion of M in uniform 2-norm
     is countably generated;
(ii) every factor fibre (M_x,tau_x) is diffuse II1.    (D3-1)
```

Then every bounded positive trace on every fibre gap `K_x/J_x` vanishes.
Consequently restriction to the centre identifies

```text
T(M) = {a |-> integral_K tau_x(a_x) dmu(x):
        mu a Radon probability measure on K}.          (D3-2)
```

In particular every tracial state on `M` is continuous for the uniform
`2`-norm.

Countable generation is automatic when `M` is the uniform tracial
completion of a separable C-star algebra. No common ambient factor, local
triviality, hyperfiniteness, property Gamma, or uniform isomorphism type is
assumed. Matrix fibres and mixed matrix/diffuse bundles are not covered.