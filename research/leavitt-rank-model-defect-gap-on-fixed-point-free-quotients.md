---
rg: 2
id: leavitt-rank-model-defect-gap-on-fixed-point-free-quotients
kind: claim
title: On the fixed-point-free quotient of a rank model of the binary Leavitt unit group, the two-root defect is bounded below by a universal constant
distinct_from:
  two-root-identity-is-corner-local-for-leavitt-rank-models: that is the qualitative equivalence, model by model, between triviality and a vanishing corner product; this is a uniform quantitative gap derived from it by compactness, which bounds the defect below by a fixed multiple of the part of the model that is not fixed.
  leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model: that shows the defect piece carries a nontrivial model of the same group; this bounds the size of every cylinder defect in terms of what the model does not fix.
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

**ESTABLISHED** (route `leavitt-rank-model-defect-gap-proof`; artifact Section 2; independent
re-derivation requested from `w4-vf-gate`).

**Setting.**
* `R = L_(F_2)(1,2)`, and `iota_A(g) = S[A] g T[A] + (1 - S[A]T[A])`.
* `sigma : R^x -> M^x` is a homomorphism into the units of a rank ultraproduct over a field of
  characteristic two, and `fM = Fix_r(sigma(R^x))`.
* For a proper cylinder `A`, `D_A = (sigma(iota_A(x_23(1))) - 1)(sigma(iota_A(x_12(1))) - 1)`.

**Statement.** There is a constant `c_0 > 0`, independent of `sigma`, the field and `A`, with

```text
c_0 · rk(1-f)  <=  rk((1-f) D_A)  <=  rk(1-f) / 2 ,        rk(D_A) <= rk(1-f) .
```

Moreover `(1-f) sigma (1-f)` is a fixed-point-free homomorphism, nontrivial exactly when `sigma`
is. So every nontrivial fixed-point-free model has normalized defect in `[c_0, 1/2]`, and
`c_0 <= 1/2` whenever a nontrivial model exists.

**What it uses.**
* Used:
  * corner locality, which is where "R has no rank model" enters;
  * perfection;
  * four-generation;
  * compactness over rank ultraproducts.
* Not used: property (T), fixed-ideal globality, the compressor collision.
* Because of the compactness step, `c_0` is not explicit.

**Calibration.** In `EL_3(A_X)`, the Toeplitz calibration group of
`kazhdan-groups-without-fd-reps-violate-two-root-identity`, the honest model is fixed-point-free
and has defect `0`. So the gap fails exactly where corner locality fails.
