---
rg: 2
id: fpbs-walk-rate-shape-classes-fail-proof
kind: route
title: Two forced plateaus of the walk-rate profile against the chord inequality
target: fpbs-walk-rate-shape-classes-fail
requires:
  - fpbs-critical-walk-correlation
artifacts:
  - research/artifacts/fpbs/docs/walk-rate-shape-classes-2026-09-19.md
  - experiments/fpbs-is-convexity-2026-09-17/lambda_shape.py
---

The complete proof is in Sections 1–3 of the artifact. It uses the imported
facts listed below and elementary convexity.

**Imported facts.**

* Schramm's lemma `a_n(p_c) <= rho^n` (`fpbs-critical-walk-correlation`).
* Kesten: the return probabilities `p_(2n)(o,o)` have exponential rate `rho`.
* Harris–FKG.
* Monotonicity of uniqueness (Häggström–Peres, Schonmann).

**Proof.**

1. **Plateaus.**
   * `rho <= lambda <= rho` on `(0,p_c]`, by Kesten and by monotonicity plus
     Schramm's lemma. The interval is nondegenerate because
     `p_c >= 1/(deg-1)`.
   * `lambda >= p`, via a geodesic.
   * If `p_u < 1`, then `lambda = 1` on `(p_u,1)`. Under uniqueness
     `tau >= theta^2 > 0`.
2. **Chord lemma.** Let `f` be constant `= c` on a nondegenerate subinterval.
   * A concave `f` cannot exceed `c` anywhere.
   * A convex `f` with `f <= c` cannot go below `c` anywhere.
   * Proof: pick `m` interior to the plateau and `e` in the plateau on the far
     side of `m`. Apply the chord inequality to `e`, `m` and the offending
     point.
3. **The cases.** Step 2 applied to `psi o lambda o phi^(-1)` gives (A) and (B).
   * Homeomorphisms `phi` carry nondegenerate intervals to nondegenerate
     intervals.
   * Strictly increasing `psi` preserves the order used in step 2.
4. **Domain restriction.** For (D): in the collapse scenario, every
   percolation-defined domain `{lambda < 1}`, `(0,p_u)` or `(0,p_lambda)` is
   `(0,p_c]` or `(0,p_c)`. On it `lambda` is constant.
5. **Finite-n corollary.** Fekete gives `a_n^(1/n) -> lambda` pointwise, and
   `a_n >= p^n > 0`. Convexity and concavity are closed under pointwise
   limits.

(C) is not part of the written proof. It is a computation from an exact
transfer-matrix formula, validated against the exact finite-`n` polynomials.
