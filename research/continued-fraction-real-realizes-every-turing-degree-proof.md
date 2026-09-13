---
rg: 2
id: continued-fraction-real-realizes-every-turing-degree-proof
kind: route
title: Convergents compute α_S from S, and one strict rational comparison per digit recovers S from α_S
target: continued-fraction-real-realizes-every-turing-degree
requires: []
---

Put `a_k = 1+χ_S(k−1)` for `k ≥ 1`, so every `a_k ∈ {1,2}` and `α = α_S = [0; a_1, a_2, …]`. Let `p_k/q_k` be
the convergents: `p_(−1)=1, q_(−1)=0, p_0=0, q_0=1`, and `p_k = a_k p_(k−1) + p_(k−2)`, `q_k = a_k q_(k−1) + q_(k−2)`.

1. **Irrational, in (0,1).** An infinite simple continued fraction with positive integer partial quotients
   converges to an irrational number, because rationals have finite expansions. We have `α = 1/y_1` with
   `y_1 = [a_1; a_2, …] > 1`, so `α ∈ (0,1)`.
2. **S computes α.** The convergents are computable from `χ_S`, and `|α − p_k/q_k| < 1/q_k²`. Here
   `q_k ≥ F_(k+1)` (Fibonacci), so the error bound is computable and tends to 0.
3. **α computes S.**
   - For `k ≥ 0`, `α = (p_k y + p_(k−1)) / (q_k y + q_(k−1))`, where `y = y_(k+1) = [a_(k+1); a_(k+2), …]`.
   - The tail is irrational, so `y ∈ (1,2)` if `a_(k+1) = 1` and `y ∈ (2,3)` if `a_(k+1) = 2`.
   - The Möbius map `y ↦ (p_k y + p_(k−1))/(q_k y + q_(k−1))` is strictly monotone on `y > 0`, since
     `p_k q_(k−1) − p_(k−1) q_k = ±1`.
   - So `a_(k+1)` is decided by comparing `α` with the rational number `r_k = (2p_k + p_(k−1))/(2q_k + q_(k−1))`,
     which is the image of `y = 2`. The comparison is strict, since `α ≠ r_k`.
   - With rational approximations of `α`, the comparison terminates, and `r_k` is computable from
     `a_1, …, a_k`.
   - By induction, `α` computes every `a_k`, hence `χ_S(k−1) = a_k − 1`. ∎
