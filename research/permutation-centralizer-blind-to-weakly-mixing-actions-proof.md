---
rg: 2
id: permutation-centralizer-blind-to-weakly-mixing-actions-proof
kind: route
title: A permutation in the embedded crossed product normalizes the Cartan, so it is a full-group element, and weak mixing forces its cocycle to be a constant in the centralizer
target: permutation-centralizer-blind-to-weakly-mixing-actions
requires: []
---

Notation as in the claim. `A = L^∞(X)`, `R` is the orbit relation, `D_𝒰 = Π_(n→𝒰) D_(k_n)`.

**Step 1 (the Cartan is recovered).** The action is essentially free, so `A` is maximal abelian in
`M` (Păunescu, Example 1.11 and the paragraph after Definition 1.10: `L^∞(X) ⋊ G ≅ M(E_α)`, and `A` is
maximal abelian in `M(E)`). `Θ(M) ∩ D_𝒰` is an abelian subalgebra of `Θ(M)` containing `Θ(A)`, hence
equals `Θ(A)`.

**Step 2 (a commuting permutation is a normalizer).** Let `w ∈ Θ(M) ∩ 𝒮_𝒰` commute with `σ(Γ)`.
Permutation matrices normalize diagonal matrices, so `w D_𝒰 w^* = D_𝒰`. Also `w Θ(M) w^* = Θ(M)`.
Hence `w` normalizes `Θ(M) ∩ D_𝒰 = Θ(A)`, and `x = Θ^(−1)(w)` lies in the normalizer `N_M(A)`. By
Păunescu, p. 6 ("any u ∈ N(A) is of the form a·u_θ, where a ∈ U(A) and θ ∈ [E]"), `x = a u_φ` with
`a ∈ U(A)` and `φ ∈ [R]`. The decomposition is unique: `a u_φ = a' u_(φ')` gives
`u_(φ'φ^(−1)) ∈ A`, which forces `φ' = φ` and then `a' = a`.

**Step 3 (commutation).** For `γ ∈ Γ`, `u_γ a u_φ u_γ^* = (γ·a) u_(γφγ^(−1))`. Commutation and
uniqueness give `γ·a = a` and `γφγ^(−1) = φ`. `Γ` acts ergodically, being weakly mixing, so `a = λ`
is a scalar of modulus `1`.

**Step 4 (the cocycle).** Write `φ(x) = c(x)·x` with `c : X → G` measurable, unique by freeness.
`φ(γx) = γφ(x)` and freeness give `c(γx) = γ c(x) γ^(−1)`. So `c` is `Γ`-equivariant for the
conjugation action, and `c_*μ` is a conjugation-invariant probability measure on the countable set
`G`. It has no mass on infinite `Γ`-conjugacy classes, since their points would all carry equal mass.
For a finite class `C`, the set `c^(−1)(C)` is `Γ`-invariant, so by ergodicity `c` takes values in a
single finite class `C` almost everywhere. The sets `c^(−1)(g')`, `g' ∈ C`, then form a finite partition
permuted by `Γ`. Their indicators span a finite-dimensional `Γ`-invariant subspace of `L²(X)`. Weak
mixing leaves no nonconstant vectors there, so `|C| = 1`. So `c ≡ c_0` with `γ c_0 γ^(−1) = c_0` for
all `γ`, i.e. `c_0 ∈ C_G(Γ)` and `φ = c_0`.

**Step 5 (the scalar).** `w = λ σ(c_0)`, and `w σ(c_0)^(−1) = λ·1` is a permutation. Its trace
`λ` is real and nonnegative, and `|λ| = 1`, so `λ = 1` and `w = σ(c_0)`.

Conversely `σ(C_G(Γ)) ⊆ Θ(M) ∩ C_(𝒮_𝒰)(σ(Γ))`. ∎

**The consequence.** For `g ∈ G`, Theorem 4.1 puts `σ(g) σ(c) σ(g)^(−1) = σ(g c g^(−1))` in
`C_(𝒮_𝒰)(σ(Γ))`. It lies in `Θ(M)`, so by the identity it is `σ(c')` with `c' ∈ C_G(Γ)`. `σ` is
injective (a trace-zero representation), so `g c g^(−1) = c'`. That is normality of `C_G(Γ)`,
Kun--Thom Theorem B, already true when `G` is sofic, which it is whenever it has a sofic action.
