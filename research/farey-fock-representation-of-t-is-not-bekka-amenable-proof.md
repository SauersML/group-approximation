---
rg: 2
id: farey-fock-representation-of-t-is-not-bekka-amenable-proof
kind: route
title: "Ad M on HS(F) splits as the vacuum line plus Sym^m(D_2) ⊗ conj Sym^n(D_2) (m+n ≥ 1), tempered for PSU(1,1); restriction to the lattice PSL_2(Z) and Kesten give a gap, so almost invariant densities approach P_Ω; a vacuum-fixing g preserves the one-particle norm, commutes with J_0, maps z into H^2, and the argument principle makes it Möbius"
target: farey-fock-representation-of-t-is-not-bekka-amenable
requires:
  - lifted-thompson-t-farey-fock-twist-bound
  - thompson-t-is-isomorphic-to-ppsl2z
---

The notation is as in the target and in `lifted-thompson-t-farey-fock-twist-bound`.

## Imports

- (J1) From `lifted-thompson-t-farey-fock-twist-bound` (statement (W) and its proof, imports
  (I2)–(I4)): `M` exists with `M(g)W(f)M(g)^* = W(g·f)`; Powers–Størmer
  `‖a^{1/2} − b^{1/2}‖_2² ≤ ‖a − b‖_1`.
- (J2) *Fock space, recalled.* The complex Hilbert space `(H, J_0)` is `H_+`, the functions
  `Σ_{n≥1} a_n z^n` with norm `‖f‖² = Σ n|a_n|²` (up to a fixed constant). The map is
  `φ ↦ ` its positive-frequency part. `F = ⊕_{m≥0} Sym^m(H_+)` with vacuum `Ω` spanning
  `Sym^0`. For a unitary `u` on `H_+`, the second quantization `Γ(u) = ⊕ Sym^m(u)` fixes `Ω` and
  satisfies `Γ(u)W(f)Γ(u)^* = W(uf)`. `⟨Ω, W(f)Ω⟩ = exp(−‖f‖²/4)` (fixed normalization).
- (J3) *Weight-2 discrete series (Bargmann 1947; Lang, SL_2(R), Ch. IX).* `f ↦ f'` is a unitary
  isomorphism (up to a constant) from `H_+` onto the Bergman space `A²(D)`, and it intertwines
  `f ↦ f ∘ γ^{-1} − f(γ^{-1}(0))` with the weight-2 action `F ↦ (F ∘ γ^{-1})·(γ^{-1})'`.
  This is the holomorphic discrete series `D_2` of `PSU(1,1)`, which is square-integrable, so
  `D_2 ≤ λ_G` for `G = PSU(1,1)`.
- (J4) *Weak containment (Bekka–de la Harpe–Valette, Kazhdan's Property (T), Appendix F; Dixmier,
  C*-algebras, 18.1).*
  - Fell absorption: `λ_G ⊗ π ≅ (dim π)·λ_G` for every unitary `π` (BdlHV, Cor. E.2.6).
  - Weak containment passes to tensor products, direct sums, subrepresentations and
    restrictions to closed subgroups.
  - For a closed subgroup `L ≤ G`, `λ_G|_L` is a multiple of `λ_L`.
- (J5) *Hulanicki–Kesten (BdlHV, Thm. G.3.2).* A discrete group `Λ` is amenable iff
  `1_Λ ≺ λ_Λ`. `PSL_2(Z) ≅ Z/2 * Z/3` is non-amenable (it contains a free subgroup).
- (J6) *Finite Blaschke products (Garnett, Bounded Analytic Functions, Ch. II).* A function
  holomorphic on `D`, continuous on the closed disk and unimodular on `|z| = 1` is a finite
  Blaschke product, and its number of zeros is the winding number of its boundary values.

## Step 1. The conjugation representation and its restriction to `Γ`

- `Ad M(g): ξ ↦ M(g)ξM(g)^*` on `HS(F)` does not see the phase of `M(g)`. So it is a genuine
  unitary representation of `T`, and it preserves densities and the trace norm.
- Conjugation commutes with functional calculus: `Ad M(g)(ρ^{1/2}) = (Ad M(g)ρ)^{1/2}`.
- Let `γ ∈ Γ = PSL_2(Z)`, acting by a Möbius map of the disk (the circle identification of the
  target). If `f ∈ H_+`, it extends holomorphically to `D`, and so does `f ∘ γ^{-1}`. So
  `γ·f` stays in `H_+` modulo constants, i.e. `γ` acts `J_0`-linearly. The Dirichlet integral is
  conformally invariant, so it acts unitarily. Call this unitary `u_γ`; by (J3), `γ ↦ u_γ` is the
  restriction to `Γ` of the strongly continuous representation `D_2` of `G = PSU(1,1)`.
- By (J2), `Γ(u_γ)` implements `γ`. By the uniqueness in Shale's theorem (J1),
  `M(γ) = (phase)·Γ(u_γ)`. Hence `Ad M(γ) = Ad Γ(u_γ)` on `HS(F)`, and `Ad M(γ)P_Ω = P_Ω`.

## Step 2. Temperedness off the vacuum

- Under `HS(F) ≅ F ⊗ F̄`, `|a⟩⟨b| ↦ a ⊗ b̄`, the operator `Ad Γ(u)` becomes `Γ(u) ⊗ conj Γ(u)`.
  So, as a representation of `G`,
  `HS(F) = ⊕_{m,n≥0} P_{m,n}` with `P_{m,n} = Sym^m(D_2) ⊗ conj(Sym^n(D_2))` and
  `P_{0,0} = C·P_Ω`.
- Let `m ≥ 1`. Then `Sym^m(D_2) ≤ D_2 ⊗ D_2^{⊗(m−1)}`. By (J3), `D_2 ≤ λ_G`. By (J4),
  `P_{m,n} ≺ λ_G ⊗ (D_2^{⊗(m−1)} ⊗ conj Sym^n(D_2))`, which is a multiple of `λ_G`.
- Let `m = 0` and `n ≥ 1`. Then `conj(D_2) ≤ conj(λ_G) ≅ λ_G` (inversion `x ↦ x^{-1}` on
  `L²(G)` for unimodular `G`), and the same argument applies.
- So `σ := ⊕_{m+n≥1} P_{m,n}` satisfies `σ ≺ λ_G`.

## Step 3. Spectral gap for the lattice

- By (J4), `σ|_Γ ≺ λ_G|_Γ`, which is a multiple of `λ_Γ`. So `σ|_Γ ≺ λ_Γ`.
- If `σ|_Γ` had almost invariant unit vectors for `S_Γ`, then `1_Γ ≺ σ|_Γ ≺ λ_Γ`, which
  contradicts (J5). So there is `κ > 0` with `max_{s∈S_Γ} ‖σ(s)η − η‖ ≥ κ‖η‖` for all `η`.
- *Proof of (1).* Write a unit `ξ = aP_Ω + η` with `η ∈ σ`. Since `P_Ω` is `Γ`-fixed and the
  splitting is `Γ`-invariant, `Ad M(s)ξ − ξ = σ(s)η − η`. So `‖η‖ ≤ κ^{-1} m`, where
  `m = max_{s∈S_Γ} ‖Ad M(s)ξ − ξ‖_2`.
- If `a = 0`, then `1 = ‖η‖ ≤ κ^{-1}m`, and `‖ξ − P_Ω‖ ≤ 2 ≤ 2κ^{-1}m`. Otherwise put
  `c = a/|a|`. Then `‖ξ − cP_Ω‖ ≤ ‖η‖ + (1 − |a|) ≤ ‖η‖ + ‖η‖² ≤ 2‖η‖`, using
  `1 − |a| ≤ 1 − |a|² = ‖η‖²` and `‖η‖ ≤ 1`. This gives (1).

## Step 4. Vacuum rigidity, statement (2)

- Suppose `M(g)Ω = λΩ` with `|λ| = 1`. For every `f ∈ H`,
  `⟨Ω, W(g·f)Ω⟩ = ⟨Ω, M(g)W(f)M(g)^*Ω⟩ = ⟨M(g)^*Ω, W(f)M(g)^*Ω⟩ = ⟨Ω, W(f)Ω⟩`.
  By (J2), `‖g·f‖ = ‖f‖`. So `g` preserves the one-particle metric `ω(·, J_0·)` (up to the sign
  convention) as well as `ω`.
- Then `ω(gf, J_0 gk) = ω(f, J_0 k) = ω(gf, gJ_0 k)` for all `f, k`. Since `g` is invertible and
  `ω` is nondegenerate, `J_0 g = g J_0`.
- Extend `g` complex-linearly to `H ⊗ C = H^{1/2}(S^1; C)/C`. It commutes with `J_0 ⊗ 1`, so it
  preserves both eigenspaces: the positive-frequency part and the negative-frequency part.
- The function `z` is smooth, so `z ∈ H ⊗ C`, and it lies in the positive-frequency part. Hence
  `h := z ∘ g^{-1}` (this is `g^{-1}` written as a circle map in the `z`-coordinate) lies, modulo
  constants, in the positive-frequency part. So `ĥ(n) = 0` for all `n < 0`.
- `h` is continuous, so its Poisson extension is `Σ_{n≥0} ĥ(n) z^n`. It is holomorphic on `D`,
  continuous on the closed disk, and unimodular on the boundary.
- By (J6) it is a finite Blaschke product. The number of zeros equals the winding number of `h`,
  which is the degree of the orientation-preserving homeomorphism `g^{-1}`, namely `1`.
- A degree-one Blaschke product is `e^{iθ}(z − a)/(1 − āz)`, an element of `PSU(1,1)`. So `g` is a
  single Möbius map `A`.
- `g` agrees with some element `A_i ∈ PSL_2(Z)` on each piece, and each piece is a nondegenerate
  arc. Two Möbius maps that agree on an arc are equal, so `A = A_i` for all `i`. Hence `g ∈ Γ`.

## Step 5. `Γ ≠ T`

- `T` is simple and infinite (Cannon–Floyd–Parry), and `Γ^{ab} = Z/6 ≠ 0`, so `Γ` is not simple.
- So the inclusion `Γ ≤ T` is proper. Fix `g_0 ∈ T ∖ Γ`.
- By Step 4, `M(g_0)Ω ∉ CΩ`. Hence `d := ‖Ad M(g_0)P_Ω − P_Ω‖_2 > 0`, because
  `Ad M(g_0)P_Ω` is the projection onto `C·M(g_0)Ω`.

## Step 6. Proof of (3)

- Let `ρ` be a density with `‖Ad M(s)ρ − ρ‖_1 ≤ ε` for all `s ∈ S_Γ ∪ {g_0}`. Put `ξ = ρ^{1/2}`,
  a unit vector of `HS(F)`.
- By Step 1 and Powers–Størmer (J1), `‖Ad M(s)ξ − ξ‖_2 ≤ ε^{1/2}` for these `s`.
- By (1) there is `|c| = 1` with `‖ξ − cP_Ω‖_2 ≤ r := 2κ^{-1}ε^{1/2}`. Then
  `d = ‖Ad M(g_0)(cP_Ω) − cP_Ω‖ ≤ ‖Ad M(g_0)(cP_Ω − ξ)‖ + ‖Ad M(g_0)ξ − ξ‖ + ‖ξ − cP_Ω‖`,
  which is at most `2r + ε^{1/2} = (1 + 4κ^{-1})ε^{1/2}`.
- So `ε ≥ ε_0 := (d/(1 + 4κ^{-1}))² > 0`. This is (3) for the set `S_Γ ∪ {g_0}`.
- *Passage to `δ`.* Each element of `S_Γ ∪ {g_0}` is a word of length at most `L` in `p(S)^{±1}`.
  `Ad M` acts isometrically on trace class, so `‖Ad M(w)ρ − ρ‖_1 ≤ L·δ(ρ)` for such a word `w`
  (inverses cost the same). Hence `δ(ρ) ≥ ε_0/L` for every density, and `δ_* ≥ ε_0/L > 0`.

## Where the target's "Not claimed" heuristic fails

- The target said that `PSL_2(Z)` fixes the vacuum, so no obstruction comes from it. That is true
  of the vacuum line alone. But the vacuum is the only place where the gap fails: `PSL_2(Z)` is a
  lattice in `PSU(1,1)`, and every particle sector is tempered. So `PSL_2(Z)` forces almost
  invariant densities onto the vacuum, and a single non-Möbius element of `T` then breaks them.
