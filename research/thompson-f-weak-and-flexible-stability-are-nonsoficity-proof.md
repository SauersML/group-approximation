---
rg: 2
id: thompson-f-weak-and-flexible-stability-are-nonsoficity-proof
kind: route
title: Corrections of F are commuting pairs, and a sharp commutator transfer inequality makes every variant fail on sofic approximations
target: thompson-f-weak-and-flexible-stability-are-nonsoficity
requires:
  - thompson-f-sofic-iff-relator-system-unstable
artifacts:
  - research/artifacts/thompson-f-stability-variants-2026-09-16.md
---

Full proof: artifact, Sections 1--4. Numbering follows the claim.

- **Fact.** A nontrivial normal subgroup of `F` contains `F'` (Cannon--Floyd--Parry, Theorem 4.3). So every
  homomorphism `F -> Sym(t)` sends `(a, b)` to a commuting pair, and solutions of `R` are commuting pairs.
- **Transfer inequality (artifact Lemma 2.1).** Follow `x -> B^-1x -> A^-1 -> B -> A`. The four steps
  agree for `(A', B')` unless the current point lies in `E_B`, `E_A`, `E_B`, `E_A` respectively. Each step
  is a bijection of `[n]`, so at most `2(|E_A| + |E_B|)` points fail. Sharpness is an exhaustive check,
  `experiments/thompson-f-stability-variants-2026-09-16/transfer_check.py`; the proof does not use it.
- **Approximations (artifact Lemmas 3.1--3.2).**
  - The restriction of an almost-homomorphism to `S` is a stability challenge.
  - The restriction of a separating one is a sofic approximation, and `delta`-strong for large `n`.
  - `delta`-strong solutions for all `delta` give a separating almost-homomorphism.
  - Partial homomorphisms eventually solve `R`.
- **Definitional implications.** `4a => 4b => 4d` and `4a => 4c => 4d` (Bradford Remark 1.5), and
  `5a => 5b => 5c => 6`.
- **`1 => 2`.** Direction `1 => 2` of `thompson-f-sofic-iff-relator-system-unstable`: the required claim.
- **`2 => 3`.** A `min(delta, 1/15)`-strong solution is a `delta`-solution, because `l(R_j) <= 14`.
- **`2 => 5a`.** Correct a challenge at precision `1/m_k`, where `m_k -> infinity` is chosen from the
  relator defects.
- **`2 => 4a`.** Apply `5a` to `phi_n|_S` and extend to words: `d(phi_n(g), psi_n(g)) <= o(1) + l(w_g) max_s d`.
- **`6 => 1`, hence `5a, 5b, 5c => 1`.** On a sofic approximation `d([f_k(a), f_k(b)], id) -> 1`. Any
  homomorphic correction commutes, so the transfer inequality gives `liminf sum_s d^vf >= 1/2`.
- **`4d => 1`, hence `4a, 4b, 4c => 1`.** Partial-homomorphism corrections of a separating
  almost-homomorphism commute eventually, and the transfer inequality with `t = k_n` sends
  `d([phi_n(a), phi_n(b)], id)` to 0. This contradicts separation.
- **`3 => 1`.** If `F` is sofic, fix `epsilon < 1/4`. A `min(delta, 1/5, 1 - 4 epsilon)`-strong solution
  has `d([p_a, p_b], id) >= 4 epsilon`. A solution `epsilon`-close to it commutes, and the transfer
  inequality gives `< 4 epsilon`. So no `delta` works.
- **Unconditional directions.** Under 1, statements 3, 4b, 4d and 6 hold vacuously: there are no
  `delta`-strong solutions for `delta` below some `delta_0` (Lemma 3.1(c) and monotonicity), no separating
  almost-homomorphisms, and no sofic approximations. So `1 <=> 3 <=> 4b <=> 4d <=> 6` does not use the
  required claim; it uses only the transfer inequality and the Fact above.
