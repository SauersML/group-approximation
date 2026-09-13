---
rg: 2
id: induced-lattice-action-mixing-forces-c0-homogeneous-space-proof
kind: route
title: Pull back functions from L/Gamma, spread decay from the cocompact lattice to L, and read the Bernoulli part as a regular representation
target: induced-lattice-action-mixing-forces-c0-homogeneous-space
requires: []
---

# Proof

Notation as in the claim. The factor map `W → L/Γ`, `[l, z] ↦ lΓ`, is
`L`-equivariant and measure preserving, so pulling back embeds `L^2_0(L/Γ)` into
`L^2_0(W)` as an `L`-invariant subspace, and `π_0` is a subrepresentation of the
Koopman representation `π` of `L` on `L^2_0(W)`.

**Part 1.** Assume `Λ ↷ W` is mixing, so `⟨π_0(λ)f, g⟩ → 0` as `λ → ∞` in `Λ` for
all `f, g ∈ L^2_0(L/Γ)`. Since `Λ` is cocompact, `L = ΛC` with `C` compact. Let
`l_n → ∞` in `L` and write `l_n = λ_n c_n` with `c_n ∈ C`; then `λ_n → ∞`.
Given a subsequence, pass to a further one with `c_n → c`. Then

```text
|⟨π_0(l_n)f, g⟩ − ⟨π_0(λ_n)π_0(c)f, g⟩| <= ||π_0(c_n)f − π_0(c)f|| ||g|| → 0
```

by strong continuity, and `⟨π_0(λ_n)π_0(c)f, g⟩ → 0`. Every subsequence has a
further subsequence along which the coefficient tends to `0`, so it tends to `0`.

**Part 2.** If `S` is closed and non-compact and `f ∈ L^2_0(L/Γ)` is nonzero and
`S`-invariant, choose `s_n → ∞` in `S`; since `S` is closed, `s_n → ∞` in `L`, while
`⟨π_0(s_n)f, f⟩ = ||f||^2`. This contradicts Part 1, so `S` is ergodic. If
`N <= Γ` is normal in `L`, then for `n ∈ N` and `l ∈ L`,
`n·lΓ = l(l^(-1)nl)Γ = lΓ`, so `N` acts trivially on `L/Γ`. If `N` is infinite it
is a closed non-compact subgroup (it is discrete), and every vector of
`L^2_0(L/Γ)` is `N`-invariant. When `Γ ≠ L` the space `L/Γ` has at least two
points and carries an invariant probability measure of full support, so
`L^2_0(L/Γ) ≠ 0`, contradicting the first consequence.

**Part 3.** As an `L`-representation, `L^2(W) = Ind_Γ^L L^2(Z)`, and
`L^2(Z) = C ⊕ L^2_0(Z)`, with `Ind_Γ^L C = L^2(L/Γ)`. For the Bernoulli shift the
products `χ_F = ∏_(γ∈F) (2z_γ − 1)` over finite nonempty `F ⊆ Γ` form an orthonormal
basis of `L^2_0(Z)` permuted by `Γ`. The orbit of `F` spans a copy of
`ℓ^2(Γ/K_F)` with `K_F = {γ : γF = F}` finite. Induction in stages gives

```text
Ind_Γ^L ℓ^2(Γ/K_F) = Ind_(K_F)^L 1 = L^2(L/K_F),
```

the right-`K_F`-invariant part of `L^2(L)`, a subrepresentation of the left regular
representation. Coefficients of the regular representation are convolutions of
`L^2` functions and vanish at infinity; coefficients of a direct sum are uniform
limits of finite sums of these, so every coefficient of `π_B := Ind_Γ^L L^2_0(Z)`
vanishes at infinity on `L`. A sequence `λ_n → ∞` in the discrete subgroup `Λ` tends
to infinity in `L`. So the coefficients of `π = π_0 ⊕ π_B` along `Λ` vanish at
infinity iff those of `π_0` do, which is the stated equivalence. ∎
