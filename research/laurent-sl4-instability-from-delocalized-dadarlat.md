---
rg: 2
id: laurent-sl4-instability-from-delocalized-dadarlat
kind: route
title: A torus in a torsion centralizer plus delocalized Dadarlat vanishing refutes stability of SL_4(F_q[t^±1])
target: laurent-sl4-not-matricially-stable-for-q-at-least-4
requires:
  - weak-matricial-stability-kills-centralizer-even-cohomology
  - dadarlat-matricial-stability-obstruction
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

## Why sufficient

Let `q ≥ 4` be a prime power, `A = F_q[t,t^{-1}]` and `Λ = SL_4(A)`. Suppose, for a contradiction, that `Λ` is
point-norm matricially stable. The argument is artifact §3 and §5 ("The route"), written out here.

1. **Weak matricial stability.** The notion in the target is Dadarlat's matricial stability, as quoted in
   `dadarlat-matricial-stability-obstruction` §1. That claim also records that matricial stability implies weak
   matricial stability. So `Λ` is weakly matricially stable.

2. **`Λ` is finitely generated and linear.**
   - Linear: `Λ ⊂ GL_4(F_q(t))`.
   - `A` is Euclidean for `δ(t^k f_0) = deg f_0` (`f_0 ∈ F_q[t]`, `f_0(0) ≠ 0`). Given `f` and `g = t^k g_0 ≠ 0`,
     write `f = t^j f_1` with `f_1 ∈ F_q[t]` and `f_1 = Q g_0 + R` with `deg R < deg g_0`. Then
     `f = (t^{j−k}Q) g + t^j R` and `δ(t^j R) ≤ deg R < δ(g)`. Row reduction over a Euclidean ring gives
     `SL_4(A) = E_4(A)`.
   - `x_{ij}(a)x_{ij}(b) = x_{ij}(a+b)` and `[x_{ij}(a), x_{jk}(b)] = x_{ik}(ab)` for distinct `i, j, k` produce every
     `x_{ij}(c t^k)`, `k ∈ Z`, from those with `k ∈ {−1, 0, 1}`, hence every `x_{ij}(f)`, `f ∈ A`. So the finitely many
     `x_{ij}(c t^k)` with `c ∈ F_q`, `k ∈ {−1, 0, 1}`, generate `Λ`.

3. **A torsion element and its centralizer.**
   - `F_q^*` is cyclic of order `q − 1 ≥ 3`, so there is `a ∈ F_q^*` with `a² ≠ 1`.
   - Put `g = diag(λ_1, …, λ_4) = diag(a, a^{-1}, 1, 1)`. It has determinant `1` and finite order `ord(a)`.
   - For `X ∈ M_4(A)`, `(gX − Xg)_{ij} = (λ_i − λ_j)X_{ij}`. The values `a, a^{-1}, 1` are pairwise distinct, because
     `a² ≠ 1` gives `a ≠ ±1` and `a ≠ a^{-1}`. So `λ_i − λ_j ∈ F_q^*` whenever `λ_i ≠ λ_j`.
   - Hence `X ∈ Z_Λ(g)` iff `X = diag(x, y, h)` with `x, y ∈ A`, `h ∈ M_2(A)` and `xy·det h = 1`, which forces
     `x, y ∈ A^*`.

4. **A nonzero class in `H^2(Z_Λ(g);Q)`.**
   - `A^* = F_q^* × t^Z`, and `deg : A^* → Z`, `c t^k ↦ k`, is a homomorphism.
   - `ρ : Z_Λ(g) → Z^2`, `diag(x, y, h) ↦ (deg x, deg y)`, is a homomorphism, because block-diagonal matrices multiply
     blockwise.
   - `s_1 = diag(t, 1, t^{-1}, 1)` and `s_2 = diag(1, t, 1, t^{-1})` have determinant `1` and the block shape of step 3,
     so they lie in `Z_Λ(g)`. They commute, so `ι : Z^2 → Z_Λ(g)`, `e_i ↦ s_i`, is a homomorphism.
   - `ρ(s_1) = e_1` and `ρ(s_2) = e_2`, so `ρ∘ι = id`. Hence `ι^*∘ρ^* = id` on `H^2(Z^2;Q) ≅ Q`, and `ρ^*` embeds `Q`
     into `H^2(Z_Λ(g);Q)`.

5. **Contradiction.** By steps 1–2, `weak-matricial-stability-kills-centralizer-even-cohomology` applies to `G = Λ`
   with `K = F_q(t)`. For the finite-order `g` of step 3 and `k = 1` it gives `H^2(Z_Λ(g);Q) = 0`, contradicting
   step 4.

So `Λ` is not point-norm matricially stable: some asymptotic homomorphism `φ_n : Λ → U(k_n)` has no pointwise-close
homomorphisms. This is the target.
