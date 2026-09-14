---
rg: 2
id: locally-constant-gl-n-subgroup-not-confined-proof
kind: route
title: Conjugating by diag(u^{ε_1 N},…,u^{ε_n N}) makes conjugates of GL_n(LC(X,F_2)) intersect trivially
target: locally-constant-gl-n-subgroup-is-not-confined
requires: []
---

**Lemma A.** If `H ≤ G` and there are `k_1, k_2, … ∈ G` with `k_m H k_m^{-1} ∩ k_l H k_l^{-1} = {1}` for `m ≠ l`, then `H`,
and every subgroup of `H`, is not confined.

*Proof.* A finite `P ⊆ G \ {1}` meets at most `|P|` of the conjugates, so some conjugate avoids `P`. A set confining a
subgroup of `H` also confines `H`. ∎

**Step 1: `L ≤ G`.** An element `f ∈ L` is `Σ_i e_{C_i} g_i` for a finite clopen partition `{C_i}` and `g_i ∈ GL_n(F_2)`.
- For each `i`, the map `ψ_i(x) = (1 − e_{C_i})I + e_{C_i}x`, from `M_n(F_2)` to `M_n(R)`, is multiplicative and unital.
- It sends `e_jk(1)` to `e_jk(e_{C_i})`.
- `GL_n(F_2) = E_n(F_2)`, so `ψ_i(g_i) ∈ E_n(R)`.
- The factors `ψ_i(g_i)` commute and their product is `f`.

**Step 2: the conjugators lie in `G`.** Put `ε_i = 2i − n − 1`. These integers are distinct and `Σ_i ε_i = 0`.
- Let `c_N = diag(u^{ε_1 N}, …, u^{ε_n N})`, and put `s_i = ε_1 + … + ε_i`, so `s_0 = s_n = 0`.
- Let `d_i(a)` be the matrix with `a` at `(i,i)`, `a^{-1}` at `(i+1,i+1)` and the identity elsewhere.
- Then `c_N = ∏_{i=1}^{n−1} d_i(u^{s_i N})`, since the exponent at position `i` is `s_i − s_{i−1} = ε_i`.
- Each `d_i(a)` with `a ∈ R^×` lies in `E_n(R)` by Whitehead's identity inside the `(i,i+1)` block:
  `diag(a,a^{-1}) = w(a)w(−1)`, where `w(a) = e_12(a)e_21(−a^{-1})e_12(a) = [[0,a],[−a^{-1},0]]`.

**Step 3: the conjugates intersect trivially.**
- For `g ∈ M_n(LC(X,F_2))` and `ufu^{-1} = f∘T^{-1}`:
  `(c_N g c_N^{-1})_{ij} = u^{ε_i N} g_ij u^{−ε_j N} = (g_ij∘T^{−ε_i N}) u^{(ε_i − ε_j)N}`.
- Suppose `c_N g c_N^{-1} = c_M g' c_M^{-1}` with `g, g' ∈ L` and `N ≠ M`.
- For `i ≠ j` the exponents `(ε_i − ε_j)N` and `(ε_i − ε_j)M` differ. Every element of `R` is uniquely a finite sum
  `Σ_k f_k u^k`, so `g_ij = g'_ij = 0`.
- So `g` is an invertible diagonal matrix over `LC(X,F_2)`, and its diagonal entries are units of `LC(X,F_2)`.
- The only such unit is `1`, since a locally constant function `X → F_2` with an inverse takes only the value `1`. So `g = I`.

Lemma A applies with `k_m = c_m`. ∎

**Model tests.**
- Over `F_3` the torus `diag(LC(X,F_3^×))` commutes with every `c_N`, so Step 3 fails, as the scope note predicts.
- In a finite model `M_N(F_2)`, with `u` replaced by a permutation matrix `P` with `P^N = I`, the exponents are only defined
  mod `N` and Step 3 fails. Finite groups have only confined subgroups.
