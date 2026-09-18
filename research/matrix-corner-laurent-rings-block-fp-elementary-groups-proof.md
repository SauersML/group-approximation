---
rg: 2
id: matrix-corner-laurent-rings-block-fp-elementary-groups-proof
kind: route
title: A degree-one unit makes S a skew Laurent ring, the base detects rational scalars by det or Fuglede–Kadison, and E_N(M_k S) = E_Nk(S); in a crossed product the block C gives R ≅ M_k(χ_C R χ_C)
target: matrix-corner-laurent-rings-block-fp-elementary-groups
requires:
  - laurent-rational-symbols-block-fp-elementary-groups
  - q-algebra-elementary-quotients-contain-gl-n-q
---

Lane proof (gq-deep-adelic-1), not independently reviewed. Notation as in the target.

## Part (A)

1. **Homogeneity.**
   - **The unit.** Write `1 = Σ e_n` with `e_n ∈ S_n`. For homogeneous `a` of degree `m`, `a = a·1`
     has component `a e_n` in degree `m+n`, so `a e_n = 0` for `n != 0`. As `S` is spanned by
     homogeneous elements, `x e_n = 0` for all `x`. Taking `x = 1` gives `e_n = 0` for `n != 0`, so
     `1 ∈ S_0`.
   - **Inverses.** If `a ∈ S_d` is a unit, write `a^(-1) = Σ b_n` with `b_n ∈ S_n`. Then `a b_n` is
     the degree-`d+n` component of `1`, so `a b_n = 0` for `n != -d`, and `b_n = a^(-1)(a b_n) = 0`.
     So `a^(-1) ∈ S_(-d)`.
   - **Rational scalars.** Integers lie in `S_0`, and so do the inverses of primes. So the image of
     `Q` lies in `S_0`. It is central, because integers are central and the inverse of a central unit
     is central.
2. **S is skew Laurent.**
   - For `r ∈ S_n`, `r v^(-n) ∈ S_0`, so `S_n = S_0 v^n`.
   - `σ(b) = v b v^(-1)` is an automorphism of `S_0` (with inverse `b ↦ v^(-1) b v`), and it fixes
     `Q` pointwise.
   - `Σ b_n t^n ↦ Σ b_n v^n` is a ring isomorphism `S_0[t, t^(-1); σ] -> S`. It is multiplicative
     because `v b = σ(b) v`, and bijective by the grading.
3. **The base detects Q^x in K_1.**
   - *(a) Commutative.* `det : GL_M(S_0) -> S_0^x` is compatible with stabilization and trivial on
     `E(S_0)`. So it induces `K_1(S_0) -> S_0^x`, with `[λ] ↦ λ` for `λ ∈ Q^x ⊆ S_0^x`. So the image
     of `Q^x -> K_1(S_0)` maps onto `Q^x`.
   - *(b) Tracial.* Let `ρ : S_0 -> M` be unital with `M` a finite factor. For `X ∈ GL_M(S_0)` put
     `ψ(X) = Δ_M(ρ(X))^M`, where `Δ_M` is the Fuglede–Kadison determinant of the finite factor
     `M_M(M)` with normalized trace `τ_M`.
     - `Δ_M` is multiplicative (Fuglede–Kadison, Ann. of Math. 55 (1952) 520–530; quoted as in
       `tracial-harmonic-ring-keeps-rational-scalars-proof`), so `ψ` is a homomorphism into `R_(>0)`.
     - It is compatible with stabilization. `log|diag(Y, 1)| = diag(log|Y|, 0)` gives
       `τ_(M+1)(log|diag(Y,1)|) = (M/(M+1)) τ_M(log|Y|)`, so `ψ(diag(X, 1)) = ψ(X)`.
     - It is trivial on `E(S_0)`, which is perfect.
     - So `ψ` induces `K_1(S_0) -> R_(>0)` with `[λ] ↦ Δ_1(λ·1) = |λ|`. The image of `Q^x` therefore
       maps onto `Q_(>0)`, which is free abelian of infinite rank.

   In both cases the image of `Q^x -> K_1(S_0)` is not finitely generated.
4. **Laurent obstruction.** By steps 1–3, `laurent-rational-symbols-block-fp-elementary-groups`
   applies to `S = S_0[t^(±1); σ]`. So `E_L(S)` is not finitely presented for any `L >= 3`, nor is
   `E_L(S)/C` for finite normal `C`.
5. **Matrix rings.** Part 5 of `q-algebra-elementary-quotients-contain-gl-n-q` gives
   `E_N(M_k(S)) = E_(Nk)(S)`. A ring isomorphism `R ≅ M_k(S)` induces `E_N(R) ≅ E_N(M_k(S))`, and
   `Nk >= 3`. Finite normal subgroups correspond under this isomorphism, which gives part (A).

## Part (B)

6. **Matrix units.**
   - Choose coset representatives `T` of `Γ/Γ'`, with `1 ∈ T`, and put `e_(ts) = u_t χ_C u_s^(-1)`
     (`t, s ∈ T`). These lie in `R` by 2 and 3.
   - With the convention `u_g χ_A u_g^(-1) = χ_(gA)`,
     `e_(ts) e_(s'r) = u_t χ_C χ_(s^(-1)s'C) u_(s^(-1)s') u_r^(-1)`.
   - If `s = s'`, this is `e_(tr)`.
   - If `s != s'`, then `s^(-1)s' ∉ Γ'`, so `s^(-1)s'C` is a translate different from `C` and hence
     disjoint from it, and the product is `0`.
   - Finally `Σ_t e_(tt) = Σ_t χ_(tC) = 1`, because the translates partition `X`.

   So `R ≅ M_k(S)` with `S = χ_C R χ_C` (Jacobson's matrix-unit theorem; e.g. Lam, *Lectures on
   Modules and Rings*, §17). The unital map `q ↦ q χ_C` puts `Q` into `S`.
7. **Grading of S.**
   - `χ_C (b u_g) χ_C = χ_C b χ_(gC) u_g`, which is `0` unless `gC = C`, that is, unless `g ∈ Γ'`.
   - By 1, `S` is spanned by elements `χ_C b u_g χ_C ∈ R ∩ C(X,Q) u_g` with `g ∈ Γ'`. So `S` is
     `Γ'`-graded, hence `Z`-graded via `φ`, with `S_n` spanned by the pieces with `φ(g) = n`.
8. **A degree-one unit.** Pick `γ ∈ Γ'` with `φ(γ) = 1`. Then `v = χ_C u_γ = χ_C u_γ χ_C ∈ S_1`, and
   `v · χ_C u_(γ^(-1)) = χ_C χ_(γC) = χ_C = 1_S`. The other composite is `1_S` as well, so `v` is a
   unit of `S`.
9. **A tracial degree-zero part.** `e = ρ(χ_C)` is a nonzero idempotent of the finite factor `M`. In
   the example `ρ` is a `*`-map, so `e` is a projection. In general an idempotent of a C*-algebra is
   similar to a projection `p` (referee remark), so `eMe ≅ pMp` is a finite factor. Either way `ρ`
   restricts to a unital map `S_0 ⊆ S -> eMe`.

   For the example in 5: `M = L^∞(X, μ) ⋊ Γ` is a II_1 factor for a free ergodic action preserving
   an atomless probability measure (Murray–von Neumann). Also `μ(C) = 1/k > 0`, because the `k`
   translates of `C` partition `X` and `μ` is invariant.
10. **Conclusion.** Part (A) with hypothesis (b) applies to `R ≅ M_k(S)`.
