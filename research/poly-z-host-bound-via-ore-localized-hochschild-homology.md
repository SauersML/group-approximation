---
rg: 2
id: poly-z-host-bound-via-ore-localized-hochschild-homology
kind: route
title: Tensor the host with the opposite of the Ore division ring of kH; the diagonal resolution bounds weak dimension above by cd P, and the Hochschild resolution of kH, induced up, has top homology containing H_n(H; k)
target: poly-z-subgroups-bound-cantor-crossed-host-dimension
requires: []
---

All unmarked tensor products are over `k`. `A = M_r(B)` with `B = LC(X, k) ⋊ P`, and `kH ⊆ A` is a unital
subring (restrict the unital injective map `k[G] -> A` to `kH`). `kH` is an Ore domain with division ring of
fractions `D`. Then `D` is flat as a left and as a right `kH`-module (Ore localization). Put `E = D^op` and

    R = A ⊗ E,    s = cd_k P,    n = cd_k H.

Let `F^P_•` and `F_•` be projective resolutions of the trivial module `k` over `kP` (length `s`) and over `kH`
(length `n`).

## 1. Upper bound: `w.gl.dim R <= s`

- `R ≅ M_r(T)` with `T = B ⊗ E ≅ LC(X, E) ⋊ P`, since `LC(X, k) ⊗ E = LC(X, E)`. Matrix rings have the same weak
  dimension, so it suffices to treat `T`.
- `L = LC(X, E)` is the directed union of the rings `E^m` over finite clopen partitions, so it is von Neumann
  regular and every `L`-module is flat.
- For a left `T`-module `M`, give `M ⊗ F^P_j` the diagonal action, `f(m ⊗ x) = fm ⊗ x` and
  `u_g(m ⊗ x) = u_g m ⊗ gx`. The covariance `u_g f = (g·f) u_g` holds, so this is a `T`-module.
- *Induction.* `T ⊗_L M -> M ⊗ kP`, `u_g ⊗ m ↦ u_g m ⊗ g`, is a `T`-isomorphism. Here `T = ⊕_g u_g L` is free as a
  right `L`-module, so both sides are `⊕_g M` and the map is bijective on each summand. `T`-linearity:
  `f u_g ⊗ m = u_g ⊗ (g^(-1)·f) m ↦ f u_g m ⊗ g`, and `u_h` shifts `g` to `hg` on both sides.
- `T ⊗_L M` is flat over `T`, because `T` is flat over `L` and `M` is flat over `L`. The same holds for summands, so
  each `M ⊗ F^P_j` is flat. The complex `M ⊗ F^P_• -> M` is exact (tensor over a field), so it is a flat
  resolution of length `s`.
- Hence `Tor^T_i(N, M) = 0` for `i > s`, all `N` and `M`. ∎

## 2. A resolution of `D` over `S = kH ⊗ E`

- `S ⊆ R` via `kH ⊆ A`. `D` is a left `S`-module by `(c ⊗ e^op) · x = c x e`.
- Let `Λ = kH ⊗ kH^op ⊆ S`. The bimodule `kH` is `Λ ⊗_(kΔ) k`, where `kΔ ⊆ Λ` is the diagonal
  `h ↦ h ⊗ (h^(-1))^op`, and `Λ` is free over `kΔ`. So `Λ ⊗_(kΔ) F_•` is a projective `Λ`-resolution of `kH` of
  length `n`.
- For a left `Λ`-module `V`, `S ⊗_Λ V ≅ E ⊗_(kH^op) V`, because the factor `kH` is free of rank one. `E` is flat
  over `kH^op`, since `D` is flat as a left `kH`-module. So `S ⊗_Λ -` is exact.
- `S ⊗_Λ kH ≅ D` as `S`-modules. Hence `P_• = S ⊗_(kΔ) F_•` is a projective `S`-resolution of `D` of length `n`.

## 3. Base change to `R` is exact

- As a right `S`-module, `R = A ⊗ E ≅ A ⊗_(kH) S`.
- `S = kH ⊗ E` is free as a left `kH`-module. So a projective resolution of the right `kH`-module `A` stays one
  after `- ⊗_(kH) S`. Hence `Tor^S_i(A ⊗_(kH) S, D) ≅ Tor^(kH)_i(A, D)`.
- This vanishes for `i >= 1`, because `D` is flat as a left `kH`-module.
- So `R ⊗_S P_•` is a projective resolution of `Q = R ⊗_S D ≅ A ⊗_(kH) D`.

No hypothesis on `A` as a `kH`-module is used. This is the step that the fraction-field Koszul argument for
polynomial subrings also isolates; here `D` replaces `Frac(C)`.

## 4. The top Tor contains `H_n(H; k)`

- Let `Q' = D ⊗_(kH) A`. It is a right `R`-module: `A` acts on the right, and `e^op ∈ E` acts by left
  multiplication on `D`.
- `Tor^R_n(Q', Q) = H_n(Q' ⊗_R R ⊗_S P_•) = H_n(Q' ⊗_(kΔ) F_•) = H_n(H; Q'^ad)`. Here `Q'^ad` is `Q'` with the right
  `H`-action `(d ⊗ a) · h = h^(-1) d ⊗ a h`.
- *`D` embeds.* `D -> Q'`, `d ↦ d ⊗ 1`, is `H`-equivariant for conjugation on `D`, because
  `h^(-1) d ⊗ h = h^(-1) d h ⊗ 1`. It is injective. `Q' ≅ Σ^(-1) A` is the Ore localization of the left
  `kH`-module `A`. The class of `c ∈ kH ⊆ A` dies only if `t c = 0` for some nonzero `t ∈ kH`, which is
  impossible in the domain `kH`. Invertible denominators then give injectivity on all of `D`.
- *The trivial summand.* `k · 1 ⊆ D^ad` is a trivial submodule, so `k ⊆ Q'^ad`.
- *Left exactness in top degree.* `F_•` has length `n`, so `H_n(H; M) = ker(M ⊗_(kH) F_n -> M ⊗_(kH) F_(n-1))`.
  Each `- ⊗_(kH) F_j` is exact, so `H_n(H; -)` preserves monomorphisms.
- Hence `0 ≠ H_n(H; k) ⊆ H_n(H; Q'^ad) = Tor^R_n(Q', Q)`, and `w.gl.dim R >= n`.

With Section 1, `n <= s`. This is part 1 of the claim. ∎

## 5. Poly-Z subgroups and Thompson's F

- *Poly-Z.* Let `H` be poly-`Z` of Hirsch length `h`. Then `kH` is an iterated skew Laurent polynomial ring over
  `k`, so it is a Noetherian domain and therefore Ore on both sides (Goldie).
- `H` is a Poincaré duality group of dimension `h` (recalled), so `cd_k H = h`.
- Some subgroup `H'` of index at most `2` is orientable. It is poly-`Z` of the same Hirsch length, and
  `H_h(H'; k) ≅ k`.
- Apply part 1 to `H'` for part 2. (Over `F_2`, `H` itself works.)
- Part 3 follows. Thompson's `F` contains `Z^m` for every `m`, using `m` elements with disjoint supports.
  `Z ≀ Z` contains `Z^m`.

## 6. Checks

- `H = Z^m`: `kH` is a Laurent polynomial ring, `D = k(t_1, ..., t_m)`, and the bound `m <= s` agrees with the
  fraction-field Koszul computation (the Koszul complex is the Hochschild resolution here).
- `P = H`, `X` a point, `A = kH`: `n <= s = n`, so the bound is attained.
- `L_2 = LC(∂F_2, k) ⋊ F_2`, `s = 1`: no `k[Z^2]` inside, consistent with the direct Leavitt argument. Yet
  `L_2^x ⊇ V ⊇ Z^m`, so the bound genuinely needs linear independence of group elements.
- `UT_3(Z)` in `LC(X) ⋊ Z^2`: excluded (`3 > 2`), although commuting rank `2` would allow it. So the Hirsch bound is
  strictly stronger than a commuting-rank bound.
