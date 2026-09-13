---
rg: 2
id: graph-braid-nonzero-euler-characteristic-sigma-asymmetric
kind: claim
title: "If e(UD_n Gamma) is nonzero, the high BNSR invariants of the graph braid group B_n Gamma contain no antipodal pair"
distinct_from:
  nonzero-euler-characteristic-blocks-symmetric-sigma: that is the general statement for type F groups; this is its application to graph braid groups with the explicit dimension bound min(n, k(Gamma))
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part1.md
---

Let `Γ` be a finite connected graph, `n ≥ 1`, `k(Γ)` the number of
vertices of degree `≥ 3`, and `d = max(1, min(n, k(Γ)))`. If
`e(UD_nΓ) ≠ 0` (computed on a sufficiently subdivided `Γ`), then
`Σ^m(B_nΓ) ∩ −Σ^m(B_nΓ) = ∅` for all `m ≥ d`. In particular no map
`B_nΓ → ℤ` has a kernel of type FP.

Inputs:

- `UD_nΓ` is a finite `K(B_nΓ,1)` (Abrams 2000; Kim–Ko–Park,
  arXiv:0805.0082), so `B_nΓ` is of type F and `e(B_nΓ) = e(UD_nΓ)`;
- `cd B_nΓ ≤ min(n, k(Γ))`: `UD_nΓ` has dimension `≤ n`, and Farley–Sabalka
  (arXiv:math/0410539, AGT 5 (2005)) retract onto a complex of dimension
  `≤ k(Γ)`;
- `nonzero-euler-characteristic-blocks-symmetric-sigma`.

`e(UD_nΓ)` is the coefficient of `t^n` in
`Π_v (1 + (1 − deg v)t)(1 − t)^{−|E|}` (Gal, arXiv:math/0202143, Colloq.
Math. 89 (2001)). The route does not depend on the closed form: it uses
only the cell count of `UD_nΓ`.
