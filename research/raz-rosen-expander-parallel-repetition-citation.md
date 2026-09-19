---
rg: 2
id: raz-rosen-expander-parallel-repetition-citation
kind: route
title: Import Theorems 1 and 2 of Raz--Rosen, A Strong Parallel Repetition Theorem for Projection Games on Expanders (CCC 2012, ECCC TR10-142)
target: raz-rosen-expander-parallel-repetition-bound
requires: []
---

This is a literature import, and credit is the authors' in full. The source is
R. Raz and R. Rosen, *A Strong Parallel Repetition Theorem for Projection Games
on Expanders*, CCC 2012; ECCC TR10-142. The quotations are from text extracted
with `pypdf` on 2026-09-19 from
`eccc.weizmann.ac.il/report/2010/142/download/` (37 pages). Line breaks are
undone and symbols transcribed.

* **Abstract.** "We show that if λ is the (normalized) spectral gap of the
  underlying graph, the value of the repeated game is at most
  (1 − ϵ²)^Ω(c(λ)·n/s), where c(λ) = poly(λ); and if in addition the game is a
  projection game, we obtain a bound of (1 − ϵ)^Ω(c(λ)·n), where
  c(λ) = poly(λ), that is, a strong parallel repetition theorem (when λ is
  constant)."
* **Setting (Section 1.3).** "(biregular) bipartite expander graph … denote by
  1 − λ the second largest singular value of M. That is, λ is the (normalized)
  spectral gap of the graph."
* **Theorem 1 (Parallel Repetition For General Games).** "For every game G with
  value 1 − ϵ where ϵ < 1/2, the value of G⊗n is at most
  (1 − ϵ² · c(λ))^{n/log s} where s is the size of the answers set and
  c(λ) = (1/32)10^−12 λ²/(log(2/λ))²."
* **Theorem 2 (Parallel Repetition For Projection Games).** "For every
  projection game G with value 1 − ϵ where ϵ < 1/2, the value of G⊗n is at
  most (1 − ϵ)^{poly(λ)·n}."
* **Proof of Theorem 2, first stage.** "we may assume throughout the proof that
  n ≥ 10^4(ϵ′)^−1λ^−1. … We showed that the value of the game
  G⊗10^4(ϵ′)^−1λ^−1 is at most (1 − 10^−14 · ϵ · λ/log(2/λ))^{log(2/λ)ϵ^−1}
  ≤ 1 − 10^−15 · λ (32)", with "ϵ′ = 10^−6ϵλ/log(2/λ)" (proof of Theorem 1).
* **Proof of Theorem 2, second stage.** "We now state Rao's theorem ([23]
  Theorem 4): There is a universal constant c > 0 such that if G is a
  projection game with value at most 1 − ϵ, the value of G⊗n is at most
  (1 − cϵ²)^n. We think of the game G played n times in parallel as the game
  G⊗10^4(ϵ′)^−1λ^−1 played n · 10^−4(ϵ′)λ times in parallel. Thus combining
  Equation (32) with Rao's theorem, we obtain that the value of G⊗n is at most
  (1 − Ω(λ²))^{n·10^−4(ϵ′)λ} ≤ (1 − ϵ · poly(λ))^n."
* **Small n.** "if the theorem was false for small n it would not hold for big
  n. If there was a strategy with high success probability for small n this
  strategy could be repeated in parallel to give a contradiction for large n."

**Reading.**

1. The paper's `λ` is `1 − σ_2(M)`. On a bipartite game the constraint walk has
   spectrum `{±σ_i}`. So "walk has at most one eigenvalue `> 1 − λ`" is
   `σ_2 <= 1 − λ`, the same normalization as the target and as
   `expansion-certified-repetition-caps-deficit-ratio`.
2. Theorem 1 is used verbatim. `log` is to any fixed base `>= 2`. Only
   `log s >= 1`-type bounds up to absolute constants are used downstream.
3. *Instantiation of poly(λ) in Theorem 2.* Equation (32) gives value
   `<= 1 − 10^−15 λ` for the block game `B = G⊗k0`, `k0 = 10^4/(ϵ′λ)`.
   Rao's theorem applied to `B` then gives, per block,
   `1 − c·10^−30·λ²`. For `m = n/k0` blocks this is
   `(1 − c·10^−30 λ²)^{n/k0}`. Now `1/k0 = 10^−4 ϵ′ λ <= 1`, and Bernoulli's
   inequality `(1 − x)^p >= 1 − p x` for `p in [0,1]` gives a per-round rate
   of at most `c·10^−30 λ² · 10^−4 ϵ′ λ = c·10^−40 · ϵ λ⁴/log(2/λ)`. Every
   polynomial-degree statement of Theorem 2 in the paper comes from this
   derivation. The general-`n` form follows from the "small n" remark.
   Rao's constant satisfies `c <= 1`, since `(1 − cϵ²)^n` bounds a value
   `>= 0` at `ϵ = 1`.
