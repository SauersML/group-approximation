---
rg: 2
id: stw22-dim4-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated factorial bundles over four-dimensional bases have only uniform traces
distinct_from:
  stw22-dim3-factor-bundles-have-uniform-traces: that theorem uses the all-factor two-sphere modulus; the present theorem uses half-slack three-sphere fillings and Michael selection one degree higher.
  stw22-full-fundamental-group-trivial-bundles-finite-dimensional: that theorem treats all finite dimensions after fixing one diffuse full-fundamental-group fibre; the present theorem reaches dimension four for arbitrary nontrivial bundles and all finite-factor fibres.
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Let `K` be compact Hausdorff with covering dimension at most four, and let
`(M,E)` be a factorial tracially complete C-star algebra over `K`. Suppose
the Hilbert `C(K)`-module completion of `M` in uniform `2`-norm is
countably generated.

Then every bounded positive trace on every fibre gap `K_x/J_x` vanishes.
Consequently

```text
T(M)={a |-> integral_K tau_x(a_x) dmu(x):
      mu a Radon probability measure on K},            (AF4-5)
```

and every trace is continuous for the uniform `2`-norm.

Matrix sizes, diffuse II1 isomorphism classes, and matrix/diffuse fibre
type may vary arbitrarily. No common ambient factor, type stratification,
local triviality, hyperfiniteness, property Gamma, or metrizability of
`K` is assumed. Countable generation is automatic for uniform tracial
completions of separable C-star algebras.