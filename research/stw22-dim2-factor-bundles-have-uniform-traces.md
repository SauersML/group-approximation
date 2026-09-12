---
rg: 2
id: stw22-dim2-factor-bundles-have-uniform-traces
kind: claim
title: Countably generated factorial bundles over two-dimensional bases have only uniform traces
distinct_from:
  stw22-dim1-factor-bundles-have-uniform-traces: that theorem uses only path connectivity and equi-LC0; the present theorem supplies the loop filling needed to cross dimension two.
  stw22-two-dimensional-trivial-field-trace-continuity: that theorem assumes one fixed hyperfinite fibre; the present theorem allows arbitrary nontrivial bundles and varying separable finite factors.
  stw22-all-finite-factor-weighted-copy-uniform-loop-fillings: that is the fibrewise quantitative theorem; the present theorem applies stabilized Michael selection and the fibre-gap criterion globally.
artifacts:
  - research/artifacts/stw22-diffuse-weighted-loop-extension-audit-2026-08-30.md
  - research/artifacts/stw22-stabilized-l2-selection-audit-2026-08-30.md
---

Let `K` be compact Hausdorff with covering dimension at most two, and let
`(M,E)` be a factorial tracially complete C-star algebra over `K`.  Suppose
the Hilbert `C(K)`-module obtained by completing `M` in uniform `2`-norm is
countably generated.  Then every bounded positive trace on every fibre gap
`K_x/J_x` vanishes.  Consequently every tracial state on `M` is uniquely

```text
a |-> integral_K E(a)(x) dmu(x)
```

for a probability measure `mu` on `K`, and is uniform-`2`-norm continuous.

Countable generation is automatic for a uniform tracial completion of a
separable C-star algebra.  Thus the conclusion applies, in particular, to
factorial Bauer bundles arising from separable C-star algebras whose compact
extreme boundary has covering dimension at most two.  No common ambient
factor, hyperfiniteness, or local triviality is assumed.
