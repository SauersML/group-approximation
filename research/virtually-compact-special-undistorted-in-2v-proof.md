---
rg: 2
id: virtually-compact-special-undistorted-in-2v-proof
kind: route
title: Push undistortion through the core, the Kaloujnine-Krasner embedding and the local copies in 2V, using the exponent length on 2V
target: virtually-compact-special-groups-undistorted-in-2v
requires:
  - raags-are-undistorted-in-brin-thompson-group-2v
  - virtually-special-groups-embed-in-brin-thompson-group-2v
  - cubulated-hyperbolic-groups-are-virtually-special
  - compact-special-cube-complex-groups-embed-in-sln-z
---

Lane proof, not independently reviewed. We use the embedding
`ι : G -> N ≀ S_k -> 2V` of `virtually-raag-groups-in-2v-via-finite-extensions` (D1–D3) with
`H_0 = Ψ̂(A_Γ)`, and the exponent length `ℓ` on `2V` and the constants of
`raag-undistortion-in-2v-via-heaviest-belt-chain-proof`, Step 0. Item 1 of
`raags-are-undistorted-in-brin-thompson-group-2v` gives `|a|_{A_Γ} <= α ℓ(Ψ̂(a)) + β` for all `a ∈ A_Γ`,
with `α = ω/(4m)` and `β = ω/2`.

## Item 1

Let `H <= A_Γ` be undistorted, of finite index in `G`.
- **The core.** Its normal core `N` in `G` has finite index `k` in `G` and in `H`. So `N` is also
  undistorted in `A_Γ`: `|n|_N <= C_1 |n|_{A_Γ} + D_1`.
- **Coset representatives.** Choose them with `t_1 = 1`.
- **`ℓ` on `N`.** For `n ∈ N`, normality gives `n t_i = t_i (t_i^{-1} n t_i)`. So D2 sends `n` to
  `(t_1^{-1} n t_1, …, t_k^{-1} n t_k; id)`, and D1 sends that to
  `ι(n) = ∏_i Ψ̂(t_i^{-1} n t_i)^{(i)}`, a product of local copies on the disjoint bricks `Q_i`.
  - On `Q_i`, `h^{(i)} = κ_i h κ_i^{-1}`, where `κ_i` is canonical with exponent `(|prefix|, 0)`. By the
    chain rule, `e_z(h^{(i)}) = e_{κ_i^{-1}z}(h)` for `z ∈ Q_i`, and `e_z = 0` off `Q_i`.
  - Hence `ℓ(ι(n)) = max_i ℓ(Ψ̂(t_i^{-1} n t_i)) >= ℓ(Ψ̂(n))`, using the coordinate `i = 1`.
- **The bound on `N`.** Let `K <= 2V` be finitely generated with `ι(G) <= K`, and `S` a finite generating
  set. Then
  `|n|_N <= C_1 (α ℓ(ι(n)) + β) + D_1 <= C_1 α ℓ_S |ι(n)|_S + C_1 β + D_1`.
- **From `N` to `G`.** Let `R` be a finite set of right coset representatives of `N` in `G`, and write
  `g = n r` with `r ∈ R`.
  - `|g|_G <= |n|_G + c_R <= c_N |n|_N + c_R`.
  - `|ι(n)|_S <= |ι(g)|_S + c'_R`.
  - Together: `|g|_G <= C |ι(g)|_S + D`.
- **Reverse inequality.** It is automatic, so `ι : G -> K` is a quasi-isometric embedding. Take `K = 2V`.

## Item 2

Let `X` be compact special.
- **Local isometry.** Haglund–Wise Theorem 1.1 (imported, read at source, in
  `compact-special-cube-complex-sln-z-citation`) gives a local isometry `X -> A` to the standard cube
  complex (Salvetti complex) of a finitely generated right-angled Artin group `A_Γ`.
- **Convex lift.** A local isometry of nonpositively curved cube complexes lifts to an embedding of
  universal covers onto a convex subcomplex. This is standard (Haglund–Wise, same paper, §2), but this
  lane did not re-read it at source.
  - Convex subcomplexes are isometrically embedded for the combinatorial metric of 1-skeleta.
  - The 1-skeleton of `Ã` is the Cayley graph of `A_Γ` in the standard generators.
  - `π_1 X` acts properly and cocompactly on `X̃`.
- **Conclusion.** So `π_1 X <= A_Γ` is undistorted by Švarc–Milnor, and item 1 applies.

## Item 3

By `cubulated-hyperbolic-groups-are-virtually-special` (Agol), such a hyperbolic group has a
finite-index subgroup `F` with `X/F` compact special, since the action is cocompact. Item 2 applies. ∎

## The examples in the claim

- **`B_3`.** `B_3' ≅ F_2` and `Z(B_3) = ⟨Δ^2⟩`. `Δ^2` has abelianization image `6`, so
  `B_3' ∩ Z(B_3) = 1` and `B_3' × Z(B_3) ≅ F_2 × Z` has index 6. `F_2 × Z = A_{P_3}` is undistorted in
  itself.
- **`SL_2(Z)` and `GL_2(Z)`.** They have finite-index free subgroups, which are right-angled Artin groups.
- **Products.** If `H_i <= A_{Γ_i}` are undistorted, then `H_1 × H_2 <= A_{Γ_1 * Γ_2}` is undistorted.
