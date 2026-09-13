---
rg: 2
id: kassabov-g0-not-fp-proof
kind: route
title: Twisted cycles satisfy every short relation of Kassabov's G_0 but break a long one
target: kassabov-g0-is-not-finitely-presented
requires: []
---

Notation is as in `kassabov-g0-is-not-finitely-presented`.
- `X` is the ten-element generating set and `F(X)` the free group on it.
- `E_(i,j)` are the matrix units of `M_3`, and `e_(i,j)` those of `M_n`.
- On basis vectors `a_n e_(i+1) = e_i`, with indices mod `n`.

**Step 1: universal matrices.** Let `A = F_p<α, α', β, γ>` be the free
associative algebra. Send each generator in `X` to the elementary matrix over
`A` given by `a ↦ α`, `a^(-1) ↦ α'`, `b ↦ β`, `c ↦ γ`, and send inverses to
`e_(i,j)(-x)`. A word `w` of length `L` then gives a product `W(w)` in
`M_3(A)`, and every entry of `W(w) - I` has degree at most `L`.

For a unital ring homomorphism `φ : A -> S`, put `ev_φ(w) = M_3(φ)(W(w))`. This
is a homomorphism `F(X) -> GL_3(S)`, because `M_3(φ)` is multiplicative. So `w`
is trivial in `ev_φ(F(X))` iff every entry of `W(w) - I` lies in `ker φ`.
- **The group `G_0`.** It is `ev_φ(F(X))` for `φ = (φ_N)_(N >= 3)`, where
  `φ_N : A -> M_N(F_p)` sends `α, α', β, γ` to `a_N, a_N^(-1), e_(1,2), e_(2,1)`.
  So a word is trivial in `G_0` iff the entries of `W(w) - I` lie in every
  `ker φ_N`.
- **Twisted models.** Let `K = F_p` if `p >= 3` and `K = F_4` if `p = 2`, and
  fix `λ in K` with `λ ≠ 0, 1`.
  - For `n >= 3` put `m = floor(n/2)` and
    `a^λ_n = sum_(i ≠ m) e_(i,i+1) + λ e_(m,m+1)`.
  - It is invertible, and `(a^λ_n)^n = λ I`, since each basis vector crosses
    the weighted edge exactly once in `n` steps.
  - Let `φ^λ_n` send `α, α', β, γ` to `a^λ_n, (a^λ_n)^(-1), e_(1,2), e_(2,1)`.
    Let `H_n = ev_(φ^λ_n)(F(X)) <= GL_(3n)(K)`, marked by `X`.

**Step 2: local calculus.** Let `u` be a word in `α, α', β, γ` of length at most
`D`. Let `ψ` be either `φ_N` with `N >= 2D+3`, or `φ^λ_n` with `n >= 2D+6`.
- **No `β` or `γ`.** Then `ψ(u) = a^k`, where `a` is that model's cycle and
  `k = #α - #α'` has `|k| <= D`.
- **Some `β` or `γ`.** Write `u = u_0 x_1 u_1 ... x_r u_r`, where each
  `x_s in {β, γ}` evaluates to `e_(i_s, j_s)` with `i_s, j_s in {1,2}`, and
  each `u_s` is a word in `α, α'` of net exponent `k_s`. Use
  `a^k e_(i,j) = e_(i-k, j)`, `e_(i,j) a^k = e_(i, j+k)` and
  `e_(i,j) e_(i',j') = δ_(j,i') e_(i,j')`. Every index met along the way lies
  in `[1-D, 2+D]`. So `ψ(u) = ε_u e_(I_u, J_u)`, where:
  - `I_u = i_1 - k_0` and `J_u = j_r + k_r` are integers in `[1-D, 2+D]`,
    read mod the model size;
  - `ε_u in {0,1}` is `1` iff `j_s + k_s = i_(s+1)` for `1 <= s < r`. Both
    sides lie in `[1-D, 2+D]`, so the test mod a size of at least `2D+3` is the
    test in `Z`;
  - no `λ` enters the twisted model: the window `[1-D, 2+D]` avoids `m` and
    `m+1` mod `n` once `n >= 2D+6`.

So `ε_u`, `I_u`, `J_u` and `k` are the same in every such model.

**Step 3: short kernels agree.** Let `f = sum_u c_u u` have degree at most `D`.
By Step 2, in both models
`ψ(f) = sum_(|k| <= D) μ_k a^k + sum_(I,J in [1-D, 2+D]) ν_(I,J) e_(I,J)`,
where each `μ_k` and `ν_(I,J)` is a sum of `c_u`, the same in both models.
- Take a row `r` outside the window. It exists because the size is at least
  `2D+3`.
- In row `r` the matrix units vanish, and `a^k` has a single nonzero entry, at
  column `r+k`. These columns are distinct for `|k| <= D`. So `ψ(f) = 0` forces
  every `μ_k = 0`.
- The `e_(I,J)` are then distinct matrix units, so every `ν_(I,J) = 0`.
- Conversely, zero coefficients give `ψ(f) = 0`.

Hence `φ_N(f) = 0` iff `φ^λ_n(f) = 0`, for `N >= 2D+3` and `n >= 2D+6`.

**Step 4: short relations of `G_0` hold in `H_n`.** Let `w` be trivial in
`G_0`, of length `L`. The entries of `W(w) - I` have degree at most `L` and lie
in `ker φ_(2L+3)`. By Step 3 they lie in `ker φ^λ_n` for every `n >= 2L+6`, so
`w` is trivial in `H_n`.

**Step 5: a long relation that fails.**
- **Words for ring elements.** Over any ring, with `[g,h] = g h g^(-1) h^(-1)`
  and distinct `i, j, k`, we have `[e_(i,k)(x), e_(k,j)(y)] = e_(i,j)(xy)` and
  `e_(i,j)(x) e_(i,j)(y) = e_(i,j)(x+y)`. These identities give words:
  - for `e_(i,j)(x)` in every position, e.g. `e_(1,3)(x) = [e_(1,2)(x), e_(2,3)(1)]`
    and `e_(3,2)(x) = [e_(3,1)(1), e_(1,2)(x)]`;
  - then for every monomial and every polynomial.
  So each `r in A` has a word `ω(r)` with `W(ω(r)) = I + r E_(1,2)`. (The same
  identities show that `X` generates `G_0`.)
- **The relation.** Put `q = βγ`, `r_n = (q α^n q)^2 - q α^n q`, and
  `ω_n = ω(r_n)`.
  - *In `M_N(F_p)`.* `φ_N(q) = e_(1,1)` and
    `φ_N(q α^n q) = (a_N^n)_(1,1) e_(1,1)`, which is `e_(1,1)` or `0`. Either
    way it is idempotent, so `φ_N(r_n) = 0` for every `N`, and `ω_n` is trivial
    in `G_0`.
  - *In `M_n(K)`.* `(a^λ_n)^n = λ I` gives `φ^λ_n(q α^n q) = λ e_(1,1)`, so
    `φ^λ_n(r_n) = (λ^2 - λ) e_(1,1) ≠ 0`, and `ω_n` is nontrivial in `H_n`.

**Step 6: conclusion.** Suppose `G_0` is finitely presented. Since `X` is
finite, `G_0 = <X | w_1, ..., w_t>` for finitely many relators; let `ℓ` be the
maximum of their lengths. Take `n >= 2ℓ+6`.
- By Step 4 every `w_i` is trivial in `H_n`, so the marking `F(X) -> H_n`
  factors through `G_0`.
- `ω_n` is trivial in `G_0` by Step 5, so it is trivial in `H_n`. That
  contradicts Step 5. `∎`
