---
rg: 2
id: hls-ghost-class-never-lifts-via-cnd-restriction
kind: route
title: Restrict a boundary-vanishing class to the CND-support shift, read off its cylinder expansion, and pull the vanishing boundary class back through injective assembly and half-exactness
target: hls-ghost-class-never-lifts-to-the-bernoulli-full-shift
requires:
  - cnd-support-shift-actions-are-a-t-menable
  - cnd-support-shift-bc-and-k-amenability
  - bernoulli-shift-weak-k-equivalence-and-going-down
  - amenable-kernel-bc-transfer-and-ktop-half-exactness
  - bernoulli-bc-splits-into-host-and-cylinder-comparison
  - bernoulli-assembly-injective-beyond-the-host
  - bernoulli-pattern-expansions-are-finite
artifacts:
  - research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md
---

Full proofs: `research/artifacts/bc-cnd-support-shift-a-t-menable-2026-09-16.md`, Lemma 1.1, Lemma 5.1, Theorem C and
Section 6. Write `H = T_cnd`, `S_H` for the patterns `s = (F, a)` with `x_s ∈ H`, and `C_s = {y : y|_F = a}`. Short
names: CC = `bernoulli-bc-splits-into-host-and-cylinder-comparison`, RF = `bernoulli-assembly-injective-beyond-the-host`,
LOC = `bernoulli-pattern-expansions-are-finite`, GD = `bernoulli-shift-weak-k-equivalence-and-going-down`,
HE = `amenable-kernel-bc-transfer-and-ktop-half-exactness`.

1. **Cylinder basis on `H` (artifact, Lemma 6.1 and Corollary 6.2).**
   - `H` is closed, invariant and hereditary (`cnd-support-shift-actions-are-a-t-menable`, item 1). So `C_s ∩ H ≠ ∅`
     iff `s ∈ S_H`.
   - The `[1_(C_s ∩ H)]`, `s ∈ S_H`, form a `Z`-basis of `K_0(C_0(H \ {0}))`, and `K_1 = 0`. Spanning restricts CC item 4
     from `X^0` to `H`. Independence evaluates at a minimal pattern.
   - `δ_s ↦ e_ss ⊗ 1_(C_s ∩ H)` is an equivariant weak K-equivalence from the proper algebra `c_0(S_H)`. By GD items 2
     and 3 and naturality of assembly (HE item 3), the image of `mu_(G, C_0(H \ {0}))` is spanned by the classes
     `[1_(C_s ∩ H)]`.
   - `mu_(G, C_0(H \ {0}))` is an isomorphism (`cnd-support-shift-bc-and-k-amenability`, item 1). So every class over
     `H` is a finite cylinder combination.
2. **Ranks factor through restriction (artifact, Lemma 6.3).** For closed invariant `W` and a pattern `x ∈ W`,
   `π_x = π_x^W ∘ res_W`, and `K_0(π_x^W)[1_(C_s ∩ W)] = #{t <= x : t ∈ G s}` (RF item 1).
3. **The boundary lies in `H` (artifact, Lemma 1.1 and Theorem C).** Boundary points are limits `g_i x_(n_i)` with
   `n_i -> ∞`. Large girth makes each small subset of `A_(n_i)` a tree subset, and tree metrics are CND. So
   `∂Y \ {0} ⊆ H`, and reduced assembly at `C_0(∂Y \ {0})` is injective (`cnd-support-shift-bc-and-k-amenability`,
   item 1).
4. **Key step (artifact, Proposition 6.4).** Let `m : G \ S_H -> Z` be finitely supported with
   `b_m = Σ m_([s]) [1_(C_s ∩ ∂Y)] = 0`. Then `L_m(A_n) = Σ_(t <= x_n) m_([t]) = 0` for large `n`.
   - `w = Σ m_([s]) [1_(C_s ∩ Ŷ)]` is `mu_Ŷ(ξ)` for a topological `ξ`, pushed from the proper algebra `c_0(S_H)`.
   - `mu_∂(q_* ξ) = b_m = 0`, and `mu_∂` is injective by step 3. So `q_* ξ = 0`.
   - `0 -> C_0(U) -> C_0(Ŷ \ {0}) -> C_0(∂Y \ {0}) -> 0` is exact (Lemma 1.1). Half-exactness (HE item 3) gives
     `κ` with `ξ = ι_* κ`, so `w = ι_* mu_U(κ)`.
   - `K_0(C_0(U) ⋊_r G) = K_0(c_0(N, K(ℓ^2 G))) = ⊕_n Z`. So `r_(x_n)(w)` is the `n`-th coordinate of `mu_U(κ)`, which
     is `0` for large `n`. By step 2 with `W = Ŷ`, `r_(x_n)(w) = L_m(A_n)`.
5. **The theorem.** Let `y` have `y|_(∂Y) = 0`.
   - By step 1, `res_H(y) = Σ m'_([s]) [1_(C_s ∩ H)]` for a finitely supported `m'` on `G \ S_H`.
   - By step 2, `r_x(y) = Σ_(t <= x) m'_([t])` for patterns `x ∈ H`. Also `r_x(y) = Σ_(t <= x) n_([t])(y)` (RF item 3).
     Möbius inversion on subsets of `supp x` gives `n_([x])(y) = m'_([x])` for all `x ∈ S_H`.
   - Restriction to `∂Y` factors through `H` by step 3, so `b_(m') = y|_(∂Y) = 0`. By step 4, `L_(m')(A_n) = 0` for large
     `n`.
   - By LOC item 2 there is `d_0` with `n_([t])(y) = 0` when `diam supp t >= d_0`. Take `n` large, with
     `girth(X_n) > 4 d_0 + 1`.
   - Compare `r_(x_n)(y) = Σ_(t <= x_n) n_([t])(y)` with `L_(m')(A_n)` term by term. A small `t <= x_n` has tree-like
     support (Lemma 5.1), so `t ∈ S_H` and the terms agree. A large `t` contributes `0` to both, since `n(y)` vanishes on
     it and `m'` agrees with `n(y)` on `S_H` and is `0` off it.
   - So `r_(x_n)(y) = L_(m')(A_n) = 0` for all large `n`. QED.

**Refutation.** `hls-ghost-class-lifts-to-the-bernoulli-full-shift` asks for `y` with `y|_(∂Y) = 0` and `r_(x_n)(y) ≠ 0`
for infinitely many `n`, over a host satisfying (M) and (H-K), with `Λ = Z/p`. The theorem excludes this for every such
host.
