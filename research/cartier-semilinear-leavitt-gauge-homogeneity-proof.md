---
rg: 2
id: cartier-semilinear-leavitt-gauge-homogeneity-proof
kind: route
title: Evaluate on the cylinder S_β(K), separate Frobenius twists by Artin's independence of characters, and read gauge degree off the surviving word lengths
target: cartier-model-semilinear-leavitt-elements-are-gauge-homogeneous
requires:
  - algebraic-core-gradings-bound-homogeneous-laurent-rank
artifacts:
  - research/cartier-model-semilinear-leavitt-elements-are-gauge-homogeneous.md
---

The notation is that of the claim. Words `α = α_1 ⋯ α_j` have letters in `{0,1}^d`.
Write `S_α = S_{α_1} ⋯ S_{α_j}`.

## 0. Imports and basic facts

- **(I1) Simplicity.** `L_F(1,n)` is simple for `n >= 2` (Leavitt 1962;
  equivalently, the Leavitt path algebra of the rose with `n` petals is simple,
  Abrams–Aranda Pino 2005). So the nonzero unital representation `π` is faithful.
- **(I2) Artin.** Distinct homomorphisms from a group `G` into `K^×` are linearly
  independent over `K`. We use `G = K^× × K^×` and
  `χ_{j,l}(c,h) = c^{2^j} h^{2^l}`.
  - These are distinct for distinct `(j,l)`. If `t_1^{2^j} = t_1^{2^l}` with
    `j < l`, then, since Frobenius is injective, `t_1^{2^{l-j}-1} = 1`.
  - That makes `t_1` algebraic over `F_2`. It then lies in the perfect subfield of
    `K`, which is inside `K^2`. This contradicts `t_1` being part of a p-basis.
- **(F1) Words.** Put `e(α) = Σ_{i=1}^{j} 2^{i-1} α_i ∈ [0,2^j)^d`.
  - Induction on `j` gives `S_α f = t^{e(α)} f^{2^j}`, because
    `S_{α_1}(t^{e'} f^{2^{j-1}}) = t^{α_1 + 2e'} f^{2^j}`.
  - The map `α ↦ e(α)` is a bijection from words of length `j` onto `[0,2^j)^d`.
  - Iterating the p-basis property shows that `{t^e : e ∈ [0,2^j)^d}` is a
    `K^{2^j}`-basis of `K`. In particular it is `F_2`-linearly independent.
- **(F2) Cylinders.** Let `|β| = M`.
  - `S_β(c h) = c^{2^M} S_β(h)`.
  - `S_γ^* S_β = δ_{γβ}` for `|γ| = M`.
  - `g = Σ_{|β|=M} S_β S_β^* g`.
  - Together these give `S_β^*(c^{2^M} g) = c S_β^* g`.
- **(F3) Normal form.** `L` is spanned by the `S_α S_β^*`. The identity
  `S_α S_β^* = Σ_{|γ|=r} S_{αγ} S_{βγ}^*` lets us take all `|β| = M` for any
  sufficiently large `M`. Gauge degree is `|α| - |β|`, and this refinement
  preserves it.

## 1. (1) ⇒ (2)

Take `x ∈ L_k`, written by (F3) with all `|β| = M` and `M >= max(0,-k)`. For each
term with `|α| = M + k`, (F2) and (F1) give
`π(S_α S_β^*)(c^{2^M} g) = S_α(c S_β^* g) = c^{2^{M+k}} π(S_α S_β^*)(g)`.
So `N = M` works.

## 2. (2) ⇒ (1)

1. **Normal form at a common level.** Let `π(x)` be twist-`k` semilinear at level
   `N`. It is then semilinear at every `M >= N`, since
   `c^{2^M} = (c^{2^{M-N}})^{2^N} ↦ c^{2^{M+k}}`. Choose `M >= N` with
   `x = Σ_{|β|=M} Σ_{α ∈ A} c_{αβ} S_α S_β^*` for a finite set of words `A` and
   `c_{αβ} ∈ F_2`.
2. **Evaluate on the cylinder.** Fix `β` and put `p_j = Σ_{α ∈ A, |α|=j} c_{αβ} t^{e(α)}`.
   By (F2), `π(x)(S_β h) = Σ_j p_j h^{2^j}`.
3. **Two expressions.** Apply semilinearity with `g = S_β h`, using
   `c^{2^M} S_β h = S_β(ch)`. For all `c, h ∈ K^×`,
   `Σ_j p_j χ_{j,j}(c,h) = Σ_j p_j χ_{M+k,j}(c,h)`.
4. **Artin.** For `j ≠ M+k`, the character `χ_{j,j}` differs from every other term
   on either side. So (I2) gives `p_j = 0`.
5. **Coefficients.** By (F1) the `t^{e(α)}` with `|α| = j` are independent, so
   `c_{αβ} = 0` whenever `|α| ≠ M + k`.
6. **Conclusion.** Hence `π(x) = π(x_k)` with
   `x_k = Σ_β Σ_{|α|=M+k} c_{αβ} S_α S_β^* ∈ L_k`. By (I1), `x = x_k`. ∎

## 3. Corollaries

1. **(C1).** Multiplication `m_f` by `f` is `K`-linear, which is twist `0` at
   `N = 0`.
   - If `m_f = π(x)`, then by the Theorem `x = Σ_{|α|=|β|=M} c_{αβ} S_α S_β^*`.
   - Evaluate at `S_β(1)` using (F1). This gives
     `f t^{e(β)} ∈ V_M := span_{F_2}{t^e : e ∈ [0,2^M)^d}` for every `β`.
   - For `β = 0^M` this gives `f ∈ V_M ⊂ F_2[t]`.
   - For `β` with `e(β) = (2^M - 1)(1, …, 1)`, multiplication by `t^{e(β)}`
     shifts every monomial `t^a` of `f` to `t^{a + e(β)}`. That lies in `V_M` only
     if `a = 0`.
   - So `f ∈ F_2`.
2. **(C2).** An operator that is `K^{2^N}`-linear is twist `0` at level `N`. So the
   Theorem gives `π(L) ∩ ⋃_N End_{K^{2^N}}(K) = π(L_0)`. For `d = 1`,
   `d/dt (a^2 + t b^2) = b^2 = S_0 S_1^*(a^2 + t b^2)`.
3. **(C3).**
   - Let `u, v` be commuting units with semilinear images of twists `k_1, k_2`.
     By the Theorem, `u ∈ L_{k_1}` and `v ∈ L_{k_2}`.
   - `L` is `Z`-graded, and `L_0 = ⋃_M M_{n^M}(F_2)` is algebraic over `F_2`.
   - So `algebraic-core-gradings-bound-homogeneous-laurent-rank` (A), with
     `Γ = Z` and `s = 1`, shows that `F_2[Z^2] -> L`, `(t_1, t_2) ↦ (u, v)`, is not
     injective.
   - **Matrix case.** For `M_m(L)` acting on `K^m`, a matrix operator is twist-`k`
     semilinear iff every entry is. To see this, test on vectors supported in one
     coordinate. So each entry lies in `L_k`, and the matrix lies in the degree-`k`
     part of the grading `M_m(L)_k = M_m(L_k)`, whose core `M_m(L_0)` is locally
     finite. Apply (A) again. ∎
