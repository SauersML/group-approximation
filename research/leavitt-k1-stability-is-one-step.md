---
rg: 2
id: leavitt-k1-stability-is-one-step
kind: claim
title: For a ring with a Leavitt pair, the kernel of GL_n/E_n -> K_1 is the kernel of one stabilization, and surjective K_1-stability at n implies injective K_1-stability at n
distinct_from:
  leavitt-stabilization-kernels-are-one-step: that is the K_2 statement for Steinberg groups; this is the K_1 statement for GL_n/E_n, with the same refinement mechanism.
  leavitt-surjective-k2-stability-implies-injective: that deduces injective from surjective stability for K_2; this does the same for K_1.
---

**ESTABLISHED** through `leavitt-k1-stability-is-one-step-proof`. Lane proof, not independently reviewed.
It is elementary given the refinement surjection `α(E_n) = E_(n+1)` (Voronetsky, via
`leavitt-refinement-identifies-unstable-k2-levels`). No priority is claimed.

**Setting.** `R` has a Leavitt pair `e, f`, and `n >= 3`. `α_n(A) = T_n A U_n` is the refinement isomorphism
`M_n(R) -> M_(n+1)(R)`. `s_n : GL_n(R)/E_n(R) -> GL_(n+1)(R)/E_(n+1)(R)` is `A -> A ⊕ 1`. Put `E = diag(1, ..., 1, e)`
and `τ_e(A) = E A E* + (1 - EE*)`. Let `u` be the unit of `leavitt-surjective-k2-stability-implies-injective`, and
`U = diag(1, ..., 1, u)`.

**Statement.**
1. **Refinement absorbs a second stabilization.** `α_(n+1)(s_n(A)) = s_(n+1)(s_n(A))`. So
   `ker(GL_n/E_n -> K_1(R)) = ker s_n`.
2. **Stabilization is a twisted refinement.** `s_n = α_n ∘ τ_e` on `GL_n/E_n`. Also `τ_e = c_U` on the image of `τ_e`,
   where `c_U` is conjugation by `U`.
3. **Surjective implies injective.** If `s_n` is onto, then `s_n` is injective.

## Reading for condition (i)

- Khanh's comparison argument over `L_(F_2)(1,2)` needs `GL = E` at ranks `n - 1` and `n - 2`.
- In a relative version for `R_L`, that requirement becomes the statement that a matrix `H in GL_(n-1)` with
  `H ⊕ 1 in E_n` already lies in `E_(n-1)`. That is `K_1`-injective stability.
- By item 3 it follows from `K_1`-surjective stability, whose natural source is that `GL_1(R_L)` hits
  `K_1(R_L) = Z` through `N + 1`. See `leavitt-resolvent-frame-complex-route-to-injective-stability`.
