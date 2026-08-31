---
rg: 2
id: stw22-dim3-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated factorial bundles over three-dimensional bases have only uniform traces
distinct_from:
  stw22-dim2-factor-bundles-have-uniform-traces: that theorem uses the all-factor loop modulus and stops at covering dimension two; the present theorem adds the all-factor two-sphere modulus and reaches dimension three.
  stw22-dim3-diffuse-factor-bundles-have-uniform-traces: that theorem is the diffuse branch; the present theorem also allows matrix fibres and arbitrary variation of fibre type.
  stw22-dim3-trivial-factor-bundles-have-uniform-traces: that theorem assumes one fixed II1 fibre; the present theorem permits nontrivial bundles and varying finite factors.
artifacts:
  - research/artifacts/stw22-dim3-all-factor-bundle-breakthrough-2026-08-31.md
---

Let `K` be compact Hausdorff with covering dimension at most three, and let
`(M,E)` be a factorial tracially complete C-star algebra over `K`. Suppose
the Hilbert `C(K)`-module obtained by completing `M` in uniform `2`-norm
is countably generated.

Then every bounded positive trace on every fibre gap `K_x/J_x` vanishes.
Consequently

```text
T(M)={a |-> integral_K tau_x(a_x) dmu(x):
      mu a Radon probability measure on K},            (AF3-1)
```

and every trace is continuous for the uniform `2`-norm.

The finite factor fibres may be matrix algebras of varying sizes, diffuse
II1 factors of varying isomorphism types, or vary between the two types.
No common ambient factor, local triviality, type stratification,
hyperfiniteness, property Gamma, or metrizability of `K` is assumed.
Countable generation is automatic for uniform tracial completions of
separable C-star algebras.