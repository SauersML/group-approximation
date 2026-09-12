---
rg: 2
id: kun-thom-clifford-skew-rings-sf-from-f3-linear-soficity
kind: route
title: F_3-linear soficity of every Clifford cover makes every anti-central skew ring stably finite
target: kun-thom-clifford-skew-rings-are-stably-finite
requires:
  - kun-thom-clifford-covers-are-f3-linear-sofic
  - linear-sofic-group-algebra-is-stably-finite
  - clifford-cover-group-algebra-splits-into-wreath-and-skew-ring
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

- `F_3`-linear soficity of `E_S` makes `F_3[E_S]` stably finite (`linear-sofic-group-algebra-is-stably-finite`).
- `A_S` is a direct factor, split off by the central idempotent `(1 - eps)/2`.
- So `A_S` is stably finite.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 27 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Checked:*
- *the field (`F_3`) and the graphs (every `S`) match the target;*
- *`M_n(F_3[E_S]) = M_n(F_3[W]) × M_n(A_S)`, so a one-sided pair in `A_S`, padded with the identity, is one in `F_3[E_S]`.*
