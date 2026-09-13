---
rg: 2
id: grigorchuk-steinberg-algebra-simple-iff-char-not-two-proof
kind: route
title: The CEPSS characteristic-zero proof needs only 2 ≠ 0; their Z_2 witness works over every characteristic-2 field
target: grigorchuk-steinberg-algebra-simple-iff-char-not-two
requires:
  - cepss-nonhausdorff-steinberg-simplicity
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

Artifact §1.
1. By (S) and (B) of `cepss-nonhausdorff-steinberg-simplicity`, `A_k(𝒢)` is simple iff no nonzero element has support
   with empty interior.
2. **`char k ≠ 2`.**
   - In `lem:LCzero` the six equations force `c_b = c_c = c_d = −c_e` and `−2c_e = 0`, hence all `c_g = 0` whenever
     `2 ≠ 0` in `k`. This is the lemma's only use of characteristic.
   - `lem:zeinterior` uses characteristic only through `lem:LCzero`. Its other inputs are `lem:basisISG`,
     [St, Lemma 4.14] and `lem:Ugm`.
   - `lem:grigsingular` uses it only through `lem:zeinterior`. Its other inputs are `lem:SupportElementBoundary`,
     `lem:ssgcalc`, `prop:singularideal` and convolution.
   - So both lemmas hold for `char k ≠ 2`, and simplicity follows as in the CEPSS proof of `thm:grigsimple`(1).
3. **`char k = 2`.**
   - `f = Σ_g 1_(U_(g,1))` satisfies the six equations (`1+1 = 0`), so `supp(f)` has empty interior.
   - By the set computation in the proof of `lem:LCzero`, `f(z_e) = 1`.
   - So `f` is a nonzero singular element, and `A_k(𝒢)` is not simple by (S).
