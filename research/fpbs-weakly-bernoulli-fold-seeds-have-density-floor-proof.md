---
rg: 2
id: fpbs-weakly-bernoulli-fold-seeds-have-density-floor-proof
kind: route
title: Transfer the fold closure to random permutation models and count slots of small sets at the crossing size
target: fpbs-weakly-bernoulli-fold-seeds-have-density-floor
requires: []
artifacts:
  - research/artifacts/fpbs-weakly-bernoulli-fold-seed-floor-2026-09-17.md
  - experiments/fpbs-fold-seed-floor-2026-09-17/floor_constant.py
  - experiments/fpbs-fold-seed-floor-2026-09-17/floor_constant_out.txt
---

The complete proof is §1 and §2 of the artifact. It imports only two things:
Kechris' definition of weak containment, and `C(N, K) ≤ e^{N H(K/N)}`.

1. **Locality.** `cl(A) = ∪_T cl_T(A)`, increasing. Membership in `cl_T(A)`
   is a fixed Boolean function of the `A`-pattern on the ball `B_{2T}`.
2. **Transfer to Bernoulli (Lemma 1).** Weak containment moves the law of
   finite patterns up to `ε` in total variation. Non-free actions are first
   replaced by `α × β`, which has the same closure pattern.
3. **Cylinder (Lemma 2).** The set may be taken to be a finite-alphabet
   cylinder set.
4. **Finite models (Lemma 3).** Take random permutations `σ_a, σ_b` of `[n]`
   with iid labels. A vertex has an injective radius-`R` ball with probability
   `≥ 1 − |B_R|²/(n − |B_R|)`. On that event its pattern has the Bernoulli
   law. So `E|S_n|/n` and `E|cl_T(S_n)|/n` converge to the Bernoulli values.
5. **Sparsity (Lemma 4).** By the first moment, `C(n,m) C(2m,k) (m/n)^k`, no
   set of size `m = ⌈α n⌉` spans `⌈(1+η)m⌉` slots, with high probability,
   when `E(α, η) < 0`. For `α = 1/8, η = 4/5`, `E = −0.00983` (checked in
   `floor_constant.py`).
6. **Crossing (Lemma 5).** If `|S| < m ≤ |cl(S)|`, the sequential closure
   passes through an `m`-set with `≥ 2(m − |S|)` slots, one pair of slots
   per firing triple.
7. **Combine.** Steps 5 and 6 give `|S_n| > (1−η) m / 2` on an event of
   probability `≥ 1 − 3γ/(1−α) − o(1)`. Take expectations and let `n → ∞`,
   then `γ → 0`. This gives `μ(A) ≥ (1−η)α/2 = 1/80`.
