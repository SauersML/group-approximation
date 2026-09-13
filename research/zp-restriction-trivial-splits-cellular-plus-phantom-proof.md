---
rg: 2
id: zp-restriction-trivial-splits-cellular-plus-phantom-proof
kind: route
title: Naturality of the action automorphism, Baaj-Skandalis descent of the Euler-class invertibility, a norm idempotent, and a nilpotent-versus-invertible cone argument
target: zp-restriction-trivial-splits-cellular-plus-phantom
requires:
  - zp-algebras-with-contractible-restriction-are-cyclotomic
  - meyer-little-invariant-detects-zero-in-zp-bootstrap
  - mn-cyclic-restrictions-detect-equivariant-bootstrap
---

**Standard inputs, not re-read from source.**
- **(S1)** `KK^G` is triangulated with countable direct sums (Meyer–Nest), so
  idempotents split (Bökstedt–Neeman).
- **(S2)** Baaj–Skandalis: for finite abelian `G`, descent
  `j_G : KK^G(A, B) → KK^Ĝ(A ⋊ G, B ⋊ G)` is an isomorphism compatible with
  Kasparov products, and it sends an equivariant \*-homomorphism `f` to `f ⋊ G`.
- **(S3)** Green–Julg: `KK^G(τX, A) ≅ KK(X, A ⋊ G)`, naturally in `X` and `A`.
  Write `Φ := − ⋊ G`, and `ε_A ∈ KK^G(τΦA, A)` for the counit, so that
  `ε_A ∘ τΦ(f) = f ∘ ε_A`.
- **(S4)** Kasparov cycles for finite `G` may be taken with `G`-invariant
  operator, by averaging.

**Cited node.** From `zp-algebras-with-contractible-restriction-are-cyclotomic`:
if `Res E ≃ 0`, then in `KK^G(E, E)` the element `1 − χ` is invertible,
`N(χ) := 1 + χ + ⋯ + χ^(p−1)` acts as `0`, and `p` is invertible. The same
holds for any prime-order group in place of `G`, in particular for `Ĝ`.

**Step 1, item 1.**
- Let `x = [(ℰ, φ, F)] ∈ KK^G(A, B)` with `G`-action `U` on `ℰ` and `F`
  invariant. Let `ℰ_⋆` be `ℰ` with `ξ ⋆ b := ξβ_ω^(−1)(b)` and
  `⟨ξ, η⟩_⋆ := β_ω(⟨ξ, η⟩)`. This is `ℰ ⊗_(β_ω) B`, so
  `x ⊗ [β_ω] = [(ℰ_⋆, φ, F)]`, and `[α_ω] ⊗ x = [(ℰ, φ∘α_ω, F)]`.
- `W := U_ω^(−1) : ℰ → ℰ_⋆` has the following properties:
  - it is `B`-linear, since `U_ω^(−1)(ξb) = U_ω^(−1)(ξ) β_ω^(−1)(b)`;
  - it is isometric, since `β_ω⟨U^(−1)ξ, U^(−1)η⟩ = ⟨ξ, η⟩`;
  - it conjugates `φ∘α_ω` to `φ`, since `U_ω^(−1) φ(α_ω a) U_ω = φ(a)`;
  - it fixes `F`;
  - it commutes with every `U_g`, because `G` is abelian.

  So the two cycles are isomorphic, and `θ` is natural.
- `θ^p = [α_ω^p] = 1`.
- Exterior products of automorphisms give `θ_(A⊗B) = θ_A ⊗ θ_B`.
- On `τX` the action is trivial, so `θ = 1`.

**Step 2, descent of `θ`.**
- `j_G(θ_A) = [α_ω ⋊ G] = [Ad u_ω]`, because `α_ω(a)u_g = u_ω(a u_g)u_ω^*`.
- `V(y) := u_ω y` is a unitary right-module map from `A ⋊ G` onto `A ⋊ G`
  with left action through `Ad u_ω`. It intertwines the left actions, and
  `α̂_φ(Vy) = φ(ω) V(α̂_φ y)`.
- So `[Ad u_ω] = ω̂^(±1) · id` in `KK^Ĝ(A ⋊ G, A ⋊ G)`, where `ω̂(φ) = φ(ω)`
  is a nontrivial character of `Ĝ`.
- Forgetting the `Ĝ`-action, `Φ(θ_A) = [Ad u_ω] = 1` in `KK`.

**Step 3, item 2.**
- **(⟸)** If `1 − θ_A` is a unit, apply `Φ`. Then `0 = 1 − 1` is a unit on
  `A ⋊ G`, so `A ⋊ G ≃ 0`.
- **(⟹)** If `A ⋊ G ≃_KK 0`, the `Ĝ`-algebra `A ⋊ G` has contractible
  restriction. By the cited node for `Ĝ`, `1 − ψ` is a unit for a generating
  character `ψ`, and so for every nontrivial character: each `1 − ζ^k` is a
  unit of `Z[ζ_p, 1/p]`. So `1 − ω̂^(±1)` is a unit, and by (S2) and Step 2 so
  is `1 − θ_A`.
- The companion statement "`Res A ≃ 0` iff `1 − χ` is a unit" is the cited
  node, together with `Res(χ) = 1`.
- **Remark.** A phantom is thus exactly an object on which
  `u := (1 − χ)(1 − θ)` is a unit. `Res(u) = 0` and `Φ(u) = 0`, and both functors
  commute with homotopy colimits. So `hocolim(A →u A →u ⋯)` always has zero
  restriction and zero crossed product.

**Step 4, item 3.**
- Assume `Res E ≃ 0`, so `p` is a unit. `θ = θ_E` is central in
  `KK^G(E, E)`, by naturality. Put `e := N(θ)/p`.
- `(θ − 1)N(θ) = θ^p − 1 = 0`, so `θe = e`, `N(θ)e = pe` and `e^2 = e`.
- `N(θ)(1 − e) = 0`. In `Z[1/p][t]/(N(t)) ≅ Z[ζ_p, 1/p]` the element `1 − t`
  is a unit, so `1 − θ` is a unit on `(1 − e)E`.
- By (S1), `E ≅ eE ⊕ (1 − e)E`.
- `Res((1 − e)E)` is a retract of `Res E ≃ 0`. By Step 3,
  `(1 − e)E ⋊ G ≃ 0`, and so `E ⋊ G ≅ eE ⋊ G`.

**Step 5, `F := eE` is a trivial-action retract.**
- Here `θ_F = 1` and `Res F ≃ 0`. Put `X := ΦF`, `b := Φ(χ · id_F) ∈ KK(X, X)`
  (the dual automorphism), and `ε := ε_F`.
- On `τX` take the commuting elements `t_1 := χ · id_(τX)` and `t_2 := τ(b)`.
  Then:
  - `t_1^p = t_2^p = 1`;
  - `N(t_2) = τΦ(N(χ) · id_F) = 0`;
  - `p` is a unit.
- By (S3) naturality, and since `χ` is central,
  `ε ∘ t_2 = (χ · id_F) ∘ ε = ε ∘ t_1`.
- So `e_diag := N(t_1 t_2^(−1))/p` is an idempotent with `ε ∘ e_diag = ε`.
  Put `P := e_diag · τX` and `ε' := ε|_P`.
- **`Φ(ε')` is invertible.**
  - `Φ(τX) = X ⊗ C*(G) = ⊕_(k ∈ Z/p) X_k`, the summands cut out by the minimal
    projections of `C*(G)`. `Φ(t_1)` permutes them cyclically, `X_k → X_(k+1)`,
    and `Φ(t_2) = b` on each.
  - The unit `η` includes `X = X_0`, and `Φ(ε) ∘ η = id`.
  - From `Φ(ε) ∘ Φ(t_1) = b ∘ Φ(ε)`, `Φ(ε)` is `b^k` on `X_k`.
  - `Φ(e_diag)` projects onto the vectors fixed by `Φ(t_1) b^(−1)`, which are
    `(x_k) = (b^(−k) x_0)`. On them `Φ(ε)` is `Σ_k b^k b^(−k) x_0 = p x_0`.
  - `p` is a unit, so `x_0 ↦ (b^(−k)x_0)_k` inverts `Φ(ε')` up to `p`.

**Step 6, the cone.**
- Let `N := cone(ε')`.
- `Res(e_diag) = N(τ b^(−1))/p = 0`, so `Res P ≃ 0`, and hence `Res N ≃ 0`.
- `ΦN ≃ 0` by Step 5.
- `θ_P = 1` (a retract of `τX`) and `θ_F = 1`. In the triangle
  `P → F →^i N →^π ΣP`, `(θ − 1)_N ∘ i = 0` and `π ∘ (θ − 1)_N = 0`. So
  `(θ − 1)_N = h∘π = i∘k` for some `h`, `k`, and
  `(θ − 1)_N^2 = h∘π∘i∘k = 0`.
- By Step 3, `1 − θ_N` is a unit. A nilpotent unit forces `KK^G(N, N) = 0`, so
  `N ≃ 0` and `F ≅ P`.

**Step 7, item 4.**
- **(Triviality of `θ` implies detection.)** If `Res D ≃ 0`, `D ⋊ G ≃ 0` and
  `θ_D = 1`, then `1 − θ_D = 0` is a unit, so `D ≃ 0`.
- **(Detection implies triviality of `θ`.)** For `Res E ≃ 0`, the part
  `(1 − e)E` is a phantom, hence `0`. So `e = 1` and `θ = θe = e = 1`.
- **Nuclear case.** `(1 − e)E` is the telescope of `1 − e` on `E`. It is
  KK^G-equivalent to a nuclear algebra when `E` is nuclear, taking cones
  nuclear as in item 2 of `zp-detection-equals-meyer-nadareishvili-sufficiency-proof`.

**Step 8, item 5.**
- **(⟹)** If `E ∈ B^G`, then `(1 − e)E ∈ B^G`, since localizing subcategories
  are closed under retracts. Its little invariant is zero, so it is `0` by
  `meyer-little-invariant-detects-zero-in-zp-bootstrap`. Hence `θ = 1`.
  `E ⋊ G ∈ B` by `mn-cyclic-restrictions-detect-equivariant-bootstrap`.
- **(⟸)** `E ≅ P` is a retract of `τ(E ⋊ G)`, which lies in `B^G` when
  `E ⋊ G ∈ B`.
- **Dual.** Apply (S2) with Takai duality. `j_G` exchanges `Res` with `− ⋊ Ĝ`,
  `χ` with the action element of `Ĝ`, and `τ` with induction. Crossed products
  of type I algebras by finite groups are type I, so `j_G(B^G) = B^Ĝ`.

**Step 9, item 6.**
- **`p = 2`.** `1 − θ` is a unit and `(1 − θ)(1 + θ) = 0`, so `θ = −1`. Likewise
  `N(χ) = 1 + χ = 0`. So `θ_(D⊗D) = (−1) ⊗ (−1) = 1`, and Step 5 applies.
- **Odd `p`.** `t_1 = θ_D ⊗ 1` and `t_2 = 1 ⊗ θ_D` commute, satisfy `N = 0`,
  and `p` is a unit. So `O ⊗ O` maps to `KK^G(D⊗D, D⊗D)`, where
  `O = Z[ζ_p, 1/p]`.
- `O` is étale and Galois over `Z[1/p]`, so `O ⊗ O ≅ ∏_σ O`. The element
  `θ_(D⊗D) = t_1 t_2` has components `ζ σ(ζ)`, and `ζσ(ζ) = 1` exactly for
  `σ(ζ) = ζ^(−1)`.
- So the idempotent `e` of `D ⊗ D` is the image of that Galois idempotent, and
  the complementary components are phantoms.
