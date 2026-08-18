---
rg: 2
id: hyperlinear-implies-sofic-via-spherical-design
kind: route
title: Read the microstate as a spherical almost action, then quantize it
target: hyperlinear-implies-sofic
requires:
  - geometric-schreier-design
  - hs-defect-is-mean-square-sphere-displacement
---

Let `G` be hyperlinear, `F ⊂ G` finite, `eps > 0`, and `T` the multiplication
table of `F`.  Take `r`, `N_0`, `delta` from `geometric-schreier-design` for
`(T,eps)` and let `{U_s}` be a hyperlinear microstate of `T` with
multiplicative defect and regular-trace separation both `< delta`.

By `hs-defect-is-mean-square-sphere-displacement` the microstate *is* a
mean-square almost action of `T` on `S^{2d-1}`: each `U_s` is an isometry
preserving the uniform measure, the tested products satisfy
`E_x‖U_gU_hx - U_{gh}x‖^2 = d_2(U_gU_h,U_{gh})^2 < delta^2`, and the tested
separations satisfy `E_x‖U_wx - x‖^2 > 2 - 2delta`.  That is precisely the
hypothesis of the design theorem, whose conclusion is a labelled Schreier
graph on `N ≥ N_0` points realizing `T` within Hamming error `eps` — a sofic
model of the window.  `F` and `eps` being arbitrary, `G` is sofic.

The recoding lemma is doing real work in this route rather than decorating it:
it is what turns an operator-algebraic hypothesis into the metric-measure
hypothesis the design theorem is stated for, and it is what identifies
regular-trace separation with the anti-collision condition the codebook
construction needs.  Without it the design theorem would have no way to
receive a hyperlinear input.
