---
rg: 2
id: linear-sofic-projective-el-lifts-to-gl-rank-models-proof
kind: route
title: Pass the projective model through the adjoint and separate by the commutant bound
target: linear-sofic-projective-el-lifts-to-gl-rank-models
requires: []
artifacts:
  - research/artifacts/un-sigma-converse-2026-09-13.md
---

This is artifact §1. The two matrix estimates are the ones in
`rank-modelled-simple-rings-give-linear-sofic-projective-el-proof`, steps 2 and 3, re-derived here.

1. **Well defined.** `Ad(A) = A ⊗ (A^(-1))^T` is a homomorphism `GL_n(k) -> GL_(n^2)(k)`, and
   `Ad(λA) = Ad(A)` for `λ ∈ k^x`. For any `λ`,
   `rk(Ad A − Ad B) = rk(Ad A − Ad(λB)) <= n rk(A − λB) + n rk(A^(-1) − λ^(-1)B^(-1)) = 2n rk(A − λB)`,
   since `A^(-1) − λ^(-1)B^(-1) = −A^(-1)(A − λB)(λB)^(-1)`. Dividing by `n^2` gives
   `rk(Ad A − Ad B)/n^2 <= 2 min_λ rk(A − λB)/n`. So `d`-null sequences go to rank-null sequences, and
   `Ad` induces a homomorphism `P -> U`.
2. **Injective on `P`.** `rk(Ad A − 1) = n^2 − dim C(A)`, where `C(A)` is the commutant. Over the
   algebraic closure, `dim C(A) <= sum_μ d_μ k_μ <= n max_μ k_μ` (conjugate Jordan partitions), with
   `k_μ = dim ker(A − μ)`. So `rk(Ad A − 1)/n^2 >= min_(μ ∈ k̄) rk(A − μ)/n`.
   - For `μ ∉ k`, `k` is perfect, so `μ` has a conjugate `μ' != μ` over `k`. `A` has entries in `k`, so
     `ker(A − μ)` and `ker(A − μ')` have equal dimension, and they are independent. So `k_μ <= n/2` and
     `rk(A − μ) >= n/2`.
   - `μ = 0` gives `rk(A) = n`.
   So if `lim_omega rk(Ad A_i − 1)/n_i^2 = 0`, then `lim_omega min_(λ ∈ k^x) rk(A_i − λ)/n_i = 0`, and
   `(A_i)` is trivial in `P`.
3. **Kernel.** `sigma = Ad ∘ iota ∘ q`, with `q : EL_N(R) -> S_N` the quotient. `iota` and `Ad` are
   injective, so `ker sigma = ker q = Z_N`. ∎
