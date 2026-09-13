---
rg: 2
id: grigorchuk-steinberg-algebra-simple-iff-char-not-two
kind: claim
title: The Steinberg algebra of the Grigorchuk groupoid over a field k is simple iff char k ≠ 2
distinct_from:
  cepss-nonhausdorff-steinberg-simplicity: that imports the characteristic-zero simplicity and the Z_2 non-simplicity; this closes every characteristic, simple exactly away from 2.
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `𝒢 = 𝒢_(G,X)` be the groupoid of germs of the Grigorchuk group's self-similar action
on `X = {0,1}`, and `k` any field. Then `A_k(𝒢)` is simple iff `char k ≠ 2`.

- **`char k ≠ 2`.** The characteristic-zero proof of Clark–Exel–Pardo–Sims–Starling uses characteristic only to solve
  `c_e+c_b = c_e+c_c = c_e+c_d = c_c+c_d = c_b+c_d = c_c+c_b = 0`. Over any field those give `c_b = c_c = c_d = −c_e`
  and `−2c_e = 0`. So only the zero solution exists whenever `2 ≠ 0`, and the rest of the proof is field-free.
- **`char k = 2`.** `f = Σ_(g∈{e,b,c,d}) 1_(U_(g,1))` is nonzero (`f(z_e) = 1`) and has support
  `{z_e,z_b,z_c,z_d}`, which has empty interior. So it is a nonzero singular element.

Artifact §1. For finite fields: `A_(F_q)(𝒢)` is simple iff `q` is odd.

**Credit and bound.** CEPSS (characteristic 0 and `Z_2`); Nekrashevych, IJAC 26 (2016), Example 4.5 (characteristic 2).
The odd-characteristic case is an immediate reading of their proof, and may already be recorded in later work; this
was not checked (no web search available).

Route: `grigorchuk-steinberg-algebra-simple-iff-char-not-two-proof`.
