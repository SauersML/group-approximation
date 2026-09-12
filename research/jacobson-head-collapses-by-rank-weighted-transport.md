---
rg: 2
id: jacobson-head-collapses-by-rank-weighted-transport
kind: route
title: Apply rank-weighted transport to the Jacobson finitary kernel
target: binary-jacobson-steinberg-head-root-is-mf-invisible
requires:
  - uniform-finite-support-rank-gap-upgrades-compression-collapse
  - binary-finitary-transvection-uniformly-controls-active-rank
  - binary-jacobson-elementary-mark-is-finite-quotient-invisible
  - binary-jacobson-steinberg-cover-is-elementary
  - elementary-group-property-t-over-free-algebras
artifacts:
  - non_mf_groups_exist.tex
  - research/artifacts/rank-weighted-locally-finite-compression-2026-09-08.md
---

Set J=F_2<S,T | TS=1>, E=EL_5(J), Q=1-ST, and a=x_13(Q).
The finitary kernel is a normal SL_fin(F_2), exhausted by standard
finite special linear groups in which a is a transvection. The
uniform support estimate holds with C=4.

H=EL_3(J) on the first three coordinates has property (T). The
rank-four compression cell of the manuscript, extended by the
identity on coordinate five, gives uHu^-1<=H and c in C_E(H) with
[u c u^-1,x_23(1)]=a. Thus a belongs to D_E(H). The rank-weighted
theorem kills a in every norm-corona representation of E. The
Steinberg identification transfers this to St_5(J).

This route uses property (T). It must not be used as a
property-(T)-free proof merely because its conclusion has no
Kazhdan hypothesis in its statement.
