---
rg: 2
id: fpbs-single-letter-morse-matchings-die-on-bernoulli-proof
kind: route
title: Heights of a single-letter matching give sublevels almost invariant under Q; the Bernoulli Kesten gap forces one thick level, which the top property forbids
target: fpbs-single-letter-morse-matchings-die-on-bernoulli
requires:
  - kesten-amenable-stabilizer-uniform-gap
  - fpbs-bernoulli-morse-collapse-criterion
artifacts:
  - research/artifacts/fpbs/docs/single-letter-morse-spectral-obstruction.md
  - experiments/single-letter-morse-2026-09-17/lambda_s.py
---

Written proof, given in full in Sections 1–4 of the artifact.

1. **Heights.** Kept edges have height `0`. A removed edge `M(y)` has height `1 +` the maximum height of its children,
   as defined by (M3) of the collapse criterion. By König's lemma the height is finite a.e. The *top property*: in a
   matched cell, the matched edge is strictly highest among its `k` `s`-edges.
2. **Lemma 1.** Each removed edge of height `<= j` is the matched edge of a cell lying inside `A_j`. So straddling
   incidences have measure `<= k delta`.
3. **Lemma 2.** For `q = h_a h_b^{-1}`, each `x in A_j` with `qx notin A_j` gives a straddling incidence. So
   `mu(A_j Δ q A_j) <= 2k delta`.
4. **Lemma 3.** A level-`J` edge has `>= k - 1` non-matched incidences. Each lies in an unmatched cell or in a cell
   whose matched edge has height `> J`.
5. **Gap.** On Bernoulli, `L^2_0|Lambda_s = ⊕ l^2(Lambda_s/K)` with `K` finite. (KAG2) of
   `kesten-amenable-stabilizer-uniform-gap` then gives `n_j(1 - n_j) <= k delta/(1 - rho)` for all `j`. The same
   holds on factors, which are invariant subspaces.
6. **Conclusion.**
   - If `k delta/(1 - rho) >= 1/4`, done.
   - Otherwise the `n_j` avoid `(theta, 1 - theta)`, with `theta = 2k delta/(1 - rho)`. The first level to jump has
     mass `>= 1 - 2 theta`, and Lemma 3 gives `theta >= (k - 1)/(3k)`.
7. **Examples.** Nonamenability of `Lambda_s` in the examples is certified by Freiheitssatz witnesses printed by
   `lambda_s.py`. The fixed-price claim for `F(a,b) *_Z F(c,d)` is Gaboriau's amalgam theorem, used only as a
   calibration, not as a prerequisite.
