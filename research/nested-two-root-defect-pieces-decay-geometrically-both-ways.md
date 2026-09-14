---
rg: 2
id: nested-two-root-defect-pieces-decay-geometrically-both-ways
kind: claim
title: The nested two-root defect pieces of a Leavitt rank model shrink at every step by a factor between the defect gap and one half
distinct_from:
  leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model: that produces the nested defect pieces, each carrying a nontrivial model, with weakly decreasing ranks and no bound; this bounds the descent on both sides, proving the uniform lower bound it asked for and showing the ranks at least halve, so no limit corner of positive rank exists.
  leavitt-rank-model-defect-gap-on-fixed-point-free-quotients: that is the defect gap for one model; this iterates it through range corners of commuting cylinder defects and adds the square-zero upper bound.
artifacts:
  - research/artifacts/two-root-defect-descent-gap-2026-09-12.md
---

**ESTABLISHED** (route `nested-defect-descent-two-sided-bounds-proof`; artifact Section 3;
independent re-derivation requested from `w4-vf-gate`).

**Setting.**
* `sigma` is a characteristic-two rank model of `R^x`, `R = L_(F_2)(1,2)`, with fixed ideal `fM`.
* `D_A` is the two-root product of the pair `iota_A(x_12(1))`, `iota_A(x_23(1))`.
* `c_*` is the infimum of the normalized defect over nontrivial fixed-point-free models. It
  satisfies `c_0 <= c_* <= 1/2`.

**Statement.**
1. **Fixed-point-free models.** For pairwise disjoint proper cylinders `A_1, ..., A_(k+1)` with
   proper union, `f(k) = rk(D_(A_1) ... D_(A_k))` satisfies `c_* f(k) <= f(k+1) <= f(k)/2`. So
   `c_*^k <= f(k) <= 2^-k`.
2. **Any nontrivial model.** The nested defect pieces `Q_1 ⊇ Q_2 ⊇ ...` of
   `leavitt-two-root-defect-piece-carries-a-nontrivial-rank-model` are
   `Q_k = D_(A_k) ... D_(A_1) M` with `A_j = 0^(j-1)1000`.
   * Their ranks satisfy `delta_(k+1) <= delta_k/2`, and
     `c_*^k rk(1-f) <= delta_k <= 2^(1-k) rk(1-f)`.
   * On the fixed-point-free quotient each step shrinks by a factor in `[c_*, 1/2]`.
3. **No limit corner.** Every principal right ideal contained in all the `Q_k` has rank `0`.

**Consequence for the gate.** This is the uniform descent bound the defect-piece claim asked for,
with `c = c_*`, and it does not close the gate.
* **What does not work.** "Uniform bound plus self-similarity gives a unital approximately
  multiplicative map from `R` into a limit corner" cannot run through the nested pieces, because
  their limit has rank `0` in every model.
* **Why the bounds don't clash.** Each two-sided per-step bound is consistent with every
  `c_* <= 1/2`.
* **What a contradiction needs.** An upper bound below the gap, as in
  `leavitt-disjoint-cylinder-defects-strictly-submultiplicative`.
