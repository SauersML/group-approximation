---
rg: 2
id: near-minimal-defect-commutant-faithfulness-proof
kind: route
title: Bound the product with a commuting element from below by its range corner and from above by its kernel corner and a triangular rank count
target: near-minimal-defect-ranges-are-rank-faithful-for-the-commutant
requires:
  - nested-two-root-defect-pieces-decay-geometrically-both-ways
  - leavitt-rank-models-kazhdan-fixed-ideals-are-global
artifacts:
  - research/artifacts/halving-expansion-and-commutant-faithfulness-2026-09-12.md
---

Artifact Section 2, Lemma 2.0 and Theorem 2.1.

1. **Clopen groups are conjugate cylinder groups.** A prefix replacement `v` carries `iota_C(R^x)` onto
   `G_U`, so `Fix_r(sigma(G_U)) = sigma(v) Fix_r(sigma(iota_C(R^x))) = fM = 0` (globality, Lemma 3.0 of
   the descent artifact).
2. **Corner models.** For an idempotent `k != 0` with `kM` invariant under `sigma(G_U)`,
   `k sigma(psi(.)) k` is a nontrivial fixed-point-free model. So `rk(D_Theta k) >= c_* rk(k)` for every
   frame triple with proper union inside `U`, after moving `Theta` into the model's frame by a unit of
   `V ∩ G_U`, which preserves `kM`.
3. **Range corner.** `ZM` is invariant, so `rk(TZ) >= c_* rk(Z)`.
4. **Kernel corner.** `K = r.ann(Z)` is invariant of rank `1 - rk(Z)`, so `rk(TK) >= c_*(1 - rk(Z))`.
5. **Triangular count.** With `J = TM + K`: `rk(TM) >= rk(TK) + rk(J) - rk(K)` and
   `rk(J) - rk(K) = rk(ZTM) = rk(TZ)`, so `delta >= c_*(1 - rk(Z)) + rk(TZ)`.
6. **Near-minimality** `c_* >= delta/(1+eps)` turns 3 and 5 into the two-sided bound. Matrices follow from
   `sigma (x) 1_n`.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 13.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
