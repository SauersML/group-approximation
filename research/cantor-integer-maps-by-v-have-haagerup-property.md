---
rg: 2
id: cantor-integer-maps-by-v-have-haagerup-property
kind: claim
title: "The group C(C,Z) ⋊ V of integer-valued locally constant maps by Thompson's V has the Haagerup property"
distinct_from:
  thompson-v-has-haagerup-property: that is Farley's theorem for V itself; this asks it for the extension of V by the free abelian group C(C,Z), which is a subgroup of 2V
  brin-thompson-groups-nv-are-a-t-menable: that asserts a-T-menability of every nV; this is the special case of one explicit subgroup C(C,Z) ⋊ V ≤ 2V, which is implied by that claim but not known to imply it
artifacts:
  - research/artifacts/cantor-maps-by-v-in-brin-thompson-2026-09-16.md
---

Let `A = C(C,Z)` be the group of locally constant functions `C → Z` on the Cantor
space, and let `V` act by `(h·f)(x) = f(h^{-1}x)`. The claim is that
`G = C(C,Z) ⋊ V` admits a proper conditionally negative definite function.

This is the case `Γ = Z` of Brothier's Problem B (arXiv:1906.03789v3, Problem B,
checked 2026-09-16). It is the first open case, since for finite `Γ` the group
embeds in `V` (`twisted-power-cloning-groups-embed-in-v`, `φ0 = φ1 = id`). For
`Γ = Z/2` the group is the centralizer of an involution in `V`, as recorded in
`cantor-module-thompson-v-product-is-finitely-presented`. By
`cantor-maps-by-v-embed-in-next-brin-thompson-group`, `G ≤ 2V`, so the claim is
necessary for `brin-thompson-groups-nv-are-a-t-menable`.

Facts proved in the artifact, §3:

- `G` is finitely generated and perfect.
- `1_C` is central and undistorted, and all infinite-order elements of `A` are
  undistorted. So the Callard–Salo distortion obstruction is invisible in `G`.
- `G` is a-T-menable iff some cnd function on `G` is proper on `A`.
- A `V`-invariant cnd function on `A` has no quadratic part.

## Attempts

- **Decorated Farley charts (not proper on A).** Let `G` act on pairs `(ι, c)`,
  with `ι` a Thompson chart and `c ∈ C(C,Z)` a height decoration, by
  `(f,h)·(ι,c) = (h∘ι, c + f∘h∘ι)`.
  - The subset of standard charts decorated by constants modulo `Z·1` is
    commensurated.
  - But `|gS Δ S|` only counts carets, so it stays bounded along `n·1_{[0]}`.
  - Keeping the constants breaks commensuration: `f = 1_{[w]}` shifts the
    decoration of every deep chart below `[w]` by `1`.
  - So on almost every deep chart, a commensurated set of standard decorated charts
    must be invariant under adding constants. It then sees decorations only modulo
    constants.
- **Brick charts of 2V restricted to G (dies).** Embed `G` with `Γ = ⟨s⟩`, `s ∈ V`
  of infinite order. Then `Φ(1_{[1]})` is `(x,y) ↦ (x, s(y))` on `[1] × C` and the
  identity on `[0] × C`. Since `s ≠ 1` is not canonical on `C`, it breaks every
  brick chart `ι_u × ι_∅` with `u` below `[1]`. There are infinitely many, which is
  the codimension-one failure recorded in
  `brin-thompson-brick-charts-are-not-commensurated`. (With `s` the first-letter
  swap this is the element in the Attempts of `brin-thompson-groups-nv-are-a-t-menable`,
  but that `s` has order 2 and belongs to the `Γ = Z/2` embedding.)
- **V-invariant Lévy measures (dies as tried).** By the artifact §3(e), a
  `V`-invariant cnd function on `A` is `∫(1 - cos 2πχ(f)) dν(χ)` with `ν` a
  `V`-invariant measure on `Â∖{0}`.
  - Point characters `tδ_x`, with counting measure on an orbit, are the
    wreath-product mechanism of Brothier's Theorem A and Cornulier–Stalder–Valette.
  - Here that mechanism gives `F(1_U) = ∞`, because `U` contains infinitely many
    orbit points.
- **Gaussian white noise mod 1 (dies, heuristic).** Characters `χ(U) = W(U) mod 1`,
  with `W` white noise of intensity `δ²m`, are not almost invariant in total
  variation. The singularity step below is sketched, not written to referee standard.
  - `h_*m ≠ m` for some `h ∈ V`, for every measure `m` giving some clopen set
    finite positive mass (last sub-bullet).
  - White noises with different intensities are mutually singular (Kakutani
    dichotomy), and reduction mod 1 changes nothing at fine scales.
  - `V` has no σ-finite invariant measure giving some clopen set finite positive
    mass: an `h ∈ V` with `h[0] = [00]` forces `m([01]) = 0`, and then
    transitivity forces `m = 0` on all proper clopens.
- **Sup-norm length (not cnd).** `‖f‖_∞ ≤ |(f,h)|_S` gives linear growth along `A`.
  But `‖·‖_∞` is an ℓ^∞-type norm, and `√‖f‖_∞` is not shown to be Hilbertian.
- **Congruence truncation (partial: positional half established, 2026-09-17).**
  Pull Farley's function back along `C(C,Z) ⋊ V → C(C,Z/N) ⋊ V ≤ V` for every `N`,
  glue with summable weights, and add any cnd `ψ_0` with `ψ_0(f) ≥ F(‖f‖_∞)`, `F → ∞`.
  - The result is proper. So the target is equivalent to that sup-norm condition
    (`brothier-problem-b-reduces-to-value-range-domination`, for every residually
    finite `Γ`). What remains open is `cantor-integer-maps-sup-norm-is-cnd-dominated`.
  - The truncations alone do not supply `ψ_0` (heuristic, not written to referee
    standard). In the fibre-first coding, `h ∈ V` costs about `N·carets(h)` carets,
    while `M·1_C` costs at most about `N`. Weights with `Σ_N w_N ψ_N(h)` finite for
    every `h` keep `Σ_N w_N ψ_N(M·1_C)` bounded in `M`.
- Not settled. A proof must use characters that are non-atomic, or have an
  unboundedly growing number of atoms. Measures on boundedly-atomic characters
  cannot be almost invariant (artifact §3(g)).
