---
rg: 2
id: bilateral-laurent-haar-relation-is-sofic
kind: claim
title: The free affine action of A^n x| SL_n(A), A = F_2[x, x^(-1)], on the compact two-sided space (F_2^Z)^n with Haar measure is sofic, so its orbit relation is sofic
distinct_from:
  jacobson-haar-relation-is-laurent-affine-restriction: that realizes the Haar relation of EL_n(J) as the restriction to the unit ball of the affine action on the locally compact, infinite-measure space F_2((1/x))^n, whose soficity is open; this is the same group acting on the compact Pontryagin dual (F_2^Z)^n of A^n with Haar probability measure, where dense periodic points make the action sofic outright.
  untwisted-bilateral-symbol-enrichment-is-lef: that proves the group H_bi = GL_fin(W) x| EL_n(A) is LEF by bilateral periodic reduction; this proves that one p.m.p. action (the dual affine action) is sofic in Paunescu's sense, which group soficity does not give (kun-thom-free-nonsofic-action).
  jacobson-haar-relation-is-kazhdan-and-unsplittable: that kills treeing and amalgam routes to soficity of the one-sided Haar relation; this is a direct periodic-point approximation of the two-sided relation and uses no treeing or amalgam.
artifacts:
  - research/bilateral-laurent-haar-relation-sofic-proof.md
  - experiments/bilateral-haar-periodic-2026-09-17/check_periodic_models.py
---

**ESTABLISHED** (route `bilateral-laurent-haar-relation-sofic-proof`, swarm-0917-w15-w15-nh-pull, 2026-09-19,
unreviewed).

**Setup.**
* `A = F_2[x, x^(-1)]`, `n >= 1`, `Γ' = SL_n(A)`, `G = A^n x| Γ'` with `(w, γ)(w', γ') = (w + γ w', γ γ')`.
* `Ā = F_2^Z`, the compact group of all two-sided sequences `(y_k)_(k in Z)` (coefficient of `x^k`). It is an
  `A`-module by `(x y)_k = y_(k-1)`. `A ⊂ Ā` is the finitely supported part.
* `X_Z = Ā^n = F_2^(Z x {1..n})` with Haar measure `μ` (fair Bernoulli). `G` acts by `(w, γ).y = γ y + w`.
* `R'` is the orbit relation of this action.

**Theorem.**
1. **(Free p.m.p.)** The action preserves `μ` and is essentially free.
2. **(Sofic action.)** It is sofic in Păunescu's sense (`paunescu-sofic-action-class-permanence`, Definition 1.4).
   The sofic models are the `m`-periodic points `X_m = (A/(x^m - 1))^n = F_2^(m x n)`, on which `G` acts through
   `A -> A/(x^m - 1)` by `y -> γ̄ y + w̄`.
3. **(Sofic relation.)** `R'` is a sofic equivalence relation, by Păunescu's Proposition 1.15. Equivalently, in
   Cordeiro's Definition 2.1 (`cordeiro-sofic-relation-permanence`), every subrelation of `R'` is sofic, since the
   measured full semigroup of a subrelation is a trace-preserving sub-semigroup.

**Two quantitative inputs** (proof, Steps 2 and 3; checked in the experiment):
* If `γ ≠ 1`, then `rank_(F_2)(γ̄ - 1 on X_m) >= m - s`, where `s` is the span of any nonzero entry of `γ - 1`. So a
  periodic fixed-point set has proportion at most `2^(-(m-s))`.
* For `m` larger than the propagation of `g` plus the diameter of a window `F`, the periodic action and the bilateral
  action agree on every cylinder on `F`. The pushforward of the uniform measure on `X_m` to any window of length at
  most `m` is exactly Haar.

**Why it matters (the ambient for the Haar route).** The Haar orbit relation `R_n` of `EL_n(J)` is the restriction of
the same affine action on the one-sided space `F_2((1/x))^n` to its unit ball
(`jacobson-haar-relation-is-laurent-affine-restriction`). There, no ball is invariant under `EL_n(F_2[x])` and no
lattice is invariant under `EL_n(F_2[x^(-1)])`. On the compact two-sided space the two directions no longer compete,
because periodicity is invariant under both. So the open part of the Haar route becomes the question of whether
`R_n` can be placed class-bijectively inside this sofic ambient. That question is
`jacobson-haar-relation-lifts-into-bilateral-relation`, and it implies soficity of `EL_n(J)`
(`jacobson-el-sofic-if-haar-relation-lifts-into-bilateral`).

**Calibration.** Restricted to translations, `R'` is the tail relation (hyperfinite). Restricted to `SL_n(F_2[x])` it
is an automorphism action of a residually finite group on a compact group with dense periodic points. The theorem
gives nothing about `EL_n(J)` by itself: the two-sided space is not a factor of `X_+` and does not contain it with
positive measure.

Proof: [[bilateral-laurent-haar-relation-sofic-proof]].
