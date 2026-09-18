---
rg: 2
id: ln-completions-of-noninjective-recursions-proof
kind: route
title: Iterate psi, check that the union of kernels is saturated, and compare O_psi(B) with the completion of the quotient through the embedding criterion
target: noninjective-ln-completions-have-self-similar-bases
requires:
  - leavitt-nekrashevych-completion-embeds-and-is-fp
  - leavitt-nekrashevych-completion-simplicity-criterion
---

Lane proof (bh-algebra, 2026-09-18). Notation as in the claim.

1. **Two groupings.** Index `M_(d^N)(B)` by pairs of words of length `N`. Appending letters at the end
   commutes with grouping by the first letter (§3 of `leavitt-nekrashevych-completion-embedding-proof`,
   which needs no injectivity). So `ψ_N(b)` equals `ψ_(N−1)` applied entrywise to `ψ(b)`, and also
   `ψ` applied entrywise to `ψ_(N−1)(b)`. In particular `ker ψ_N ⊆ ker ψ_(N+1)`, so `J` is an
   increasing union of two-sided ideals, hence a two-sided ideal.
2. **Saturation.**
   - If `b ∈ J`, say `ψ_N(b) = 0`, then `ψ_(N−1)(ψ(b)_(ij)) = 0` for all `i, j`, so `ψ(J) ⊆ M_d(J)`.
   - Conversely, if every entry of `ψ(b)` lies in `J`, say `ψ_(N_(ij))(ψ(b)_(ij)) = 0`, then
     `ψ_(1+max N_(ij))(b) = 0` and `b ∈ J`.
   - So `J = ψ^(−1)(M_d(J))`, and `ψ̄(b + J) = (ψ(b)_(ij) + J)` is a well-defined injective unital
     homomorphism.
3. **`J` dies in `O_ψ(B)`.** Iterating the covariance `b = Σ_(ij) s_i ψ(b)_(ij) t_j` gives
   `b = Σ_(|μ|=|ν|=N) s_μ ψ_N(b)_(μν) t_ν`. So `ψ_N(b) = 0` forces `b = 0` in `O_ψ(B)`.
4. **Nothing else dies.**
   - The relators of `O_ψ(B)` hold in `O_(ψ̄)(B/J)`, so there is a homomorphism
     `O_ψ(B) -> O_(ψ̄)(B/J)` extending `B -> B/J`.
   - `ψ̄` is injective, so `B/J -> O_(ψ̄)(B/J)` is injective (`leavitt-nekrashevych-completion-embeds-and-is-fp`,
     part 2, whose proof does not use finite presentation of the base).
   - Hence the kernel of `B -> O_ψ(B)` is contained in `J`, and by 3 it equals `J`.
5. **Isomorphism.** By 4, `B/J -> O_ψ(B)` is well defined and satisfies the covariance relations of
   `ψ̄`, which gives `O_(ψ̄)(B/J) -> O_ψ(B)`. Both composites fix generators.
6. **Finite presentation.** §1 of `leavitt-nekrashevych-completion-embedding-proof` shows that the
   finite presentation generates all covariance relations, and it does not use injectivity.
7. **Simplicity.** Part 3 of `leavitt-nekrashevych-completion-simplicity-criterion` applies to the
   injective recursion `ψ̄` on `B/J`. It needs neither finite presentation nor any other property of
   the base. ∎
