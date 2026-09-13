---
rg: 2
id: hyperlinear-truncated-actor-covers-refute-vertex-rounding-proof
kind: route
title: Transfer the dimension-uniform rounding inequality to the exact tracial models of a truncated cover, and trap the Kazhdan intertwiner in the fixed space of an infinite kernel
target: hyperlinear-truncated-actor-covers-refute-vertex-rounding
requires: [fpbs-shalom-property-t-is-open, compressor-extension-makes-roundable-vertex-part-invariant]
---

Notation as in the target.

**Step 1 (uniform Kazhdan constant).**
- `Γ^_L = F_Γ-free group / (relations holding in G_L)`. A relation of `Γ` of length `ℓ` in `F_Γ` is a relation of
  `G` of length `ℓ`, so it holds in `G_L` once `L >= ℓ`.
- Every relation of `Γ^_L` holds in `Γ`, through `q_L`. So `Γ^_L -> Γ` in the space of marked groups, and by
  `fpbs-shalom-property-t-is-open` `Γ^_(L_0)` is Kazhdan for some `L_0`.
- For `L >= L_0`, `G_L` is a quotient of `G_(L_0)` (more relators), so `Γ^_L` is a quotient of `Γ^_(L_0)`.
- Unitary representations of a quotient are representations of `Γ^_(L_0)`. So a Kazhdan pair `(F_Γ, κ_0)` of
  `Γ^_(L_0)` is a Kazhdan pair of every `Γ^_L`, `L >= L_0`.

**Step 2 ((H1) implies (FT)_δ for every δ > 0).**
- **(FT)_δ.** There are `R, ε` such that every `(R, ε)`-almost representation `u` of `G` on `C^n` (with
  `u_1 = 1`, `||u_g u_h - u_(gh)||_2 <= ε` on the ball, `|tr u_g| <= ε` for `g ≠ e`) admits a genuine
  `π : Γ -> U(n')`, `n <= n' <= 2n`, and a contraction `x ∈ M_(n×n')` with `||x||_2 >= 1/2` and
  `max_(s ∈ F_Γ) ||u_s x - x π(s)||_2 <= δ`.
- **Proof by contradiction.** If (FT)_δ fails, pick `(k, 1/k)` counterexamples `u^(k)`.
  - Their ultraproduct is a trace-preserving actor model.
  - (H1) gives genuine `π_k` on `C^(n'_k)`, `n'_k/n_k -> 1`, with `||u^(k)_s - P π_k(s) P^*||_2 -> 0`.
  - `x = P^*`, the coordinate projection, is a contraction with `||x||_2 -> 1` and defect `-> 0`.
  - This contradicts the choice of `u^(k)` for `U`-most `k`.

**Step 3 (coordinates of a truncated cover).**
- Fix `δ = κ_0/4`, take `(R, ε)` from Step 2, and `L >= max(L_0, 3R)`. Let `τ : G_L -> U(prod_V M_m)` be
  trace-preserving, with coordinates `τ_m(s) ∈ U(m)` for `s ∈ S_G`.
- **The almost representation.** For `g ∈ B_R(G)` choose a word `w_g` of length `<= R`, and put
  `u_g = τ_m(w_g)`.
  - Two words for the same element of `G` differ by a relator of length `<= 2R <= L`, so they are equal in `G_L`.
  - The same holds for `w_g w_h` against `w_(gh)`. Hence `||u_g u_h - u_(gh)||_2 <= ε` for `V`-most `m`.
- **The trace.** If `g ≠ e` in `G`, then `w_g ≠ e` in `G_L`, so `τ(w_g)` has trace 0 and `|tr u_g| <= ε` for
  `V`-most `m`.

**Step 4 (invariant vector).**
- Step 2 gives `π_m` and `x_m` for `V`-most `m`. Put `x = (x_m)_V ∈ prod_V M_(m×m'_m)`, a nonzero contraction with
  `||x||_2 >= 1/2`.
- `π = (π_m)_V` is a homomorphism of `Γ`, and `π∘q_L` is one of `Γ^_L`. The map `ρ(γ) y = τ(γ) y π(q_L γ)^*` is a
  unitary representation of `Γ^_L` on the Hilbert space `L²` of rectangular ultraproduct matrices.
- Since `τ(s) = (u_s)_V` for `s ∈ F_Γ`, `max_s ||ρ(s)x - x||_2 <= κ_0/4 < κ_0 ||x||_2`. So `ρ` has an invariant
  vector `ξ ≠ 0`.

**Step 5 (trapping).**
- For `n ∈ N_Γ(L)`, `π(q_L n) = 1`, so `τ(n)ξ = ξ`. Let `E ∈ prod_V M_m` be the largest projection with
  `τ(n)E = E` for all `n ∈ N_Γ(L)`. Then `ξ = Eξ`.
- **The trace of `E`.** For any `m` distinct elements `n_1..n_m` of `N_Γ(L)`, put `T = m^(-1) Σ_i τ(n_i)`, so
  `TE = E`.
  - `τ(E) = τ(TE) <= ||T||_2 ||E||_2 = ||T||_2 τ(E)^(1/2)`.
  - `||T||_2^2 = m^(-2) Σ_(i,j) τ(τ(n_i^(-1) n_j)) = 1/m`, by the regular trace.
  - So `τ(E) <= 1/m`. If `N_Γ(L)` is infinite, `τ(E) = 0`, so `E = 0` and `ξ = 0`, a contradiction.

**Conclusion.** Under (H1), every `L >= max(L_0, 3R)` with `G_L` hyperlinear has `N_Γ(L)` finite. The
"equivalently" form follows from Corollary D of `compressor-extension-makes-roundable-vertex-part-invariant`,
whose summand `σ_nr` is a witness.
