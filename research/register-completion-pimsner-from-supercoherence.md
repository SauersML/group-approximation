---
rg: 2
id: register-completion-pimsner-from-supercoherence
kind: claim
title: The Pimsner sequence (P) holds for every single-register completion with a fully available spine, by Ara--Brustenga--Cortiñas and the regular supercoherence of B+
distinct_from:
  resolvent-register-units-give-rational-symbols: that states (P) as an assumption; this proves (P) for single-register completions with a spine.
  single-register-rings-divide-unit-at-finitely-many-primes: that is the divisibility theorem conditional on (P); this discharges (P) for its setting.
  abc-twisted-laurent-k-theory-fibration: that is the imported ABC theorem; this applies it to register completions and checks its hypotheses.
  eventually-rational-register-ring-is-regular-supercoherent: that is the commutative-algebra input (regular supercoherence and flatness of B+); this is the K-theory consequence.
artifacts:
  - research/artifacts/gq-gq-k2-q-register-symbols.md
  - research/artifacts/gq-referee-a-register-completion-pimsner-from-supercoherence.md
  - research/artifacts/gq-referee-b-register-completion-pimsner-from-supercoherence.md
  - research/artifacts/gq-referee-b-register-completion-rereview.md
---

**ESTABLISHED** through `register-completion-pimsner-from-supercoherence-proof` (lane proof).
The first version (bcdfabf89) had three gaps, found by `gq-referee-a` (288dbe786) and
`gq-referee-b` (27950613e): the choice of `t_+`, `K(core) ≠ K(B⁺)`, and flatness for ABC
Prop 7.1. They are repaired here following the referees' suggestions. Re-review: PASS by
`gq-referee-a` (035fee55a) and by `gq-referee-b` (852a0771f,
`gq-referee-b-register-completion-rereview.md`), the latter with the scope amendment A1,
now made: point indicators are required.

## Ingredients (verified at the source by `gq-referee-b`)
- **AGGP Lemma 2.4** (arXiv:math/0307320). "Let `D = ⊕_(i∈ℤ) D_i` be a `ℤ`-graded ring
  containing elements `t_+ ∈ D_1` and `t_- ∈ D_(-1)` such that `t_- t_+ = 1`. Then there
  is a corner isomorphism `α : D_0 -> t_+ t_- D_0 t_+ t_-` given by `α(d) = t_+ d t_-`, and
  `D = D_0[t_+, t_-; α]`."
- **ABC Theorem 3.6 and Remark 2.2** (arXiv:0903.0056), as in
  `abc-twisted-laurent-k-theory-fibration`.
- **ABC Lemma 7.2.** "Let `R` be a regular supercoherent ring and let `ϕ` be an
  automorphism of `R`. ... Then `NK_n(R[t_1,t_1^(-1),…],ϕ)_± = 0` for every `p >= 0` and
  every `n ∈ ℤ`."
- **ABC, proof of Theorem 7.6.** The corner isomorphism is replaced by the automorphism
  `ϕ̂` of the colimit `B = ϕ^(-1)L_0`, and `NK(B̃, ϕ̂)_± = NK(B ⊕ k, ϕ̂)_±` for the
  `k`-unitization. We use the same step with `k = Q`, which is central in `R`.

## Setting
A **single-register completion with a spine** is the setting of
`single-register-rings-divide-unit-at-finitely-many-primes` (part 2), with:
- letters acting on the one register by `N ↦ N + a`, `N ↦ pN + r` or `N ↦ c`;
- the coefficient ring `B⁺` as in `eventually-rational-register-ring-is-regular-supercoherent`,
  a finite product of rings `B⁺_T`;
- a **spine**: for every type `ρ`, a letter `x_ρ` with range `ρ` and full availability
  `t_(x_ρ) s_(x_ρ) = p_ρ`;
- **point indicators**: the coefficient ring contains every point indicator `δ_n`, i.e.
  contains `J = ⊕_ℕ Q` at each type (referee b, A1). This holds when some availability
  indicator such as `[N = 0]` is present and letters shift `N` in both directions, as in
  `R_cap`. It fails for `R_L`, whose coefficient ring `Q[N][(N+c)^(-1)]` has no
  idempotents. There the reset `N ↦ 0` is not flat, and (P) for `R_L` stays open.

`R` is a `Q`-algebra.

## Statement
For such `R`, with `G_n = ⊕_ρ K_n(B⁺_ρ)` and `[X] : G_n -> G_n` the transfer of the
register correspondence, there are exact sequences
`0 -> coker(1 − [X] : G_n -> G_n) -> K_n(R) -> ker(1 − [X] : G_(n−1) -> G_(n−1)) -> 0`
for every `n ∈ ℤ`. In particular `coker(1 − [X])` injects into `K_n(R)`, which is (P).

**Consequence.** Within their stated settings, and provided those have a spine and a
coefficient ring containing all point indicators,
`single-register-rings-divide-unit-at-finitely-many-primes` (part 2),
`dilation-letters-cannot-divide-the-unit-class` and
`top-determined-register-rings-cannot-divide-the-unit` hold without the assumption (P).
