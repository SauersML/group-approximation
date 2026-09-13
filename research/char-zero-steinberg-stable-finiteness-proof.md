---
rg: 2
id: char-zero-steinberg-stable-finiteness-proof
kind: route
title: A full-support invariant measure gives a stably finite reduced algebra containing the Steinberg ring; no measure gives a paradox
target: char-zero-steinberg-stably-finite-iff-invariant-measure
requires:
  - rainone-sims-minimal-groupoid-stably-finite-dichotomy
  - sims-cc-injects-into-reduced-groupoid-algebra
  - no-invariant-measure-steinberg-elementary-no-mf-quotient
artifacts:
  - research/artifacts/un-paradox-char-zero-dichotomy-2026-09-13-part3.md
---

## Why sufficient

**Measure ⇒ stably finite.**
1. By minimality an invariant probability measure has full support.
2. Integrating `k 1_A <= sum 1_(s(E_i))` and `sum 1_(r(E_i)) <= l 1_A` gives `(k - l) μ(A) <= 0`, so
   `𝒢` is completely non-paradoxical.
3. By `rainone-sims-minimal-groupoid-stably-finite-dichotomy` (minimal case), `C*_r(𝒢)` is stably
   finite.
4. In a C*-algebra, a one-sided inverse `ts = 1` makes `s*s` invertible, so `s (s*s)^(-1/2)` is an
   isometry, hence unitary, and `st = 1`.
5. With `k ⊆ C`, `A_k(𝒢) ⊆ C_c(𝒢)`, which injects into `C*_r(𝒢)`
   (`sims-cc-injects-into-reduced-groupoid-algebra`). Stable finiteness passes to unital subrings of
   matrix rings.

**No measure ⇒ not stably finite.** Item 1 of `no-invariant-measure-steinberg-elementary-no-mf-quotient`
gives `2n[1] <= n[1]` in `V(A_k(𝒢))`. So `M_n(A_k(𝒢))` has `w_i v_j = delta_ij 1`, and `w_0 v_0 = 1`
while `v_0 w_0 != 1`.
