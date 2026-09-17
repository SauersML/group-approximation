---
rg: 2
id: artin-ghost-ideal-is-intersection-of-two-principal-ideals-proof
kind: route
title: "Proof: the Salvetti complex of a spherical group, minus its top cell, is covered by copies of parabolic Salvetti complexes with nerve the Artin complex; acyclicity makes its top homology free cyclic"
target: artin-ghost-ideal-is-intersection-of-two-principal-ideals
requires:
  - spherical-artin-groups-satisfy-k-pi-1-conjecture
  - artin-complex-top-homology-is-intersection-of-ideals
  - artin-ghost-ideal-localizes-to-standard-parabolics
---

**Literature inputs.**

- The Salvetti complex `Sal_T` of an Artin group `A_T` (M. Salvetti, Topology Appl. 26 (1987);
  C. De Concini and M. Salvetti, Math. Res. Lett. 3 (1996)) is a finite regular CW complex
  with one cell `e_U` of dimension `|U|` for each `U ⊆ T` with `W_U` finite, and
  `π_1(Sal_T) = A_T`. For `U ⊆ T` spherical, `Sal_U` is the subcomplex of cells `e_{U'}`,
  `U' ⊆ U`. The closed cell `e_U` is the zonotope of `W_U` and has one vertex for each
  `w ∈ W_U`. If `W_T` is finite, `Sal_T` is homotopy equivalent to the orbit space of
  Deligne's theorem, so its universal cover `Sal̃_T` is contractible
  (`spherical-artin-groups-satisfy-k-pi-1-conjecture`).
- `A_U → A_T` is injective and `A_X ∩ A_Y = A_{X ∩ Y}` (van der Lek, thesis 1983; L. Paris,
  arXiv:1211.7339, Theorem 5.4).
- The nerve theorem for a regular CW complex covered by subcomplexes whose nonempty finite
  intersections are contractible (A. Björner, J. Combin. Theory Ser. A 102 (2003), applied to
  the barycentric subdivision). The homology isomorphism comes from the Mayer–Vietoris
  double complex of the cover, so it commutes with any cellular group action that permutes
  the cover.

**Item 1.** Let `n = |T| ≥ 2` and `W_T` finite. Choose a base vertex of `Sal̃_T`. Each cell
`e_U` has a unique lift `ẽ_U` whose vertex corresponding to `1 ∈ W_U` is the base vertex, so
the cells of `Sal̃_T` are `g·ẽ_U` with `g ∈ A_T` and `U ⊆ T`, each once. The vertices of
`g·ẽ_U` are `g·σ(w)`, `w ∈ W_U`, all in `gA_U`.

*(a) Top homology of the boundary.* Let `Y ⊆ Sal̃_T` be the subcomplex of cells `g·ẽ_U` with
`U ≠ T`. Its cellular chain complex is that of `Sal̃_T` in degrees `≤ n − 1`, and `C_n(Sal̃_T)`
is the free module `ZA_T·ẽ_T`. Since `Sal̃_T` is contractible and has no cells above
dimension `n`, `∂_n` is injective and `ker ∂_{n−1} = im ∂_n`. Hence

`H_{n−1}(Y; Z) = ker ∂_{n−1} = ∂_n(ZA_T·ẽ_T) ≅ ZA_T`,

a free left `ZA_T`-module on the class of `∂ẽ_T`.

*(b) A cover of `Y`.* For `U ⊊ T` and `g ∈ A_T` let `Y_{gA_U}` be the subcomplex of cells
`h·ẽ_{U'}` with `U' ⊆ U` and `h ∈ gA_U`. It is closed under faces: a face of `h·ẽ_{U'}` is
`hσ(w)·ẽ_{U''}` with `w ∈ W_{U'}`, `U'' ⊆ U'`, and `hσ(w) ∈ hA_{U'} ⊆ gA_U`. `Y_{gA_U}` is
`g` times the component of the base vertex in the preimage of `Sal_U`: that component
contains exactly the cells whose base vertex lies in the image of `π_1(Sal_U) = A_U`. The
map `A_U → A_T` is injective, so this component is a copy of `Sal̃_U`, which is contractible
by Deligne's theorem (a point when `U = ∅`).

The subcomplexes `Y_v`, `v = gA_{T−s}` (`s ∈ T`), cover `Y`: a cell `h·ẽ_U` with `U ≠ T` lies in
`Y_{hA_{T−s}}` for any `s ∉ U`. Let `v_i = g_iA_{T−s_i}` (`i = 1, …, t`) be distinct. A cell
`h·ẽ_{U'}` lies in every `Y_{v_i}` iff `U' ⊆ T − {s_i}` and `h ∈ v_i` for all `i`. If two `v_i`
have the same type they are disjoint cosets, and the intersection is empty. Otherwise the
types `R = {s_i}` are distinct, and `⋂ v_i` is empty or a coset `hA_{T−R}`, and then
`⋂ Y_{v_i} = Y_{hA_{T−R}}`, which is contractible. So every nonempty finite intersection is
contractible, and a family of members meets iff the cosets have a common element. The nerve
of the cover is the Artin complex `Δ(A_T)`, and `A_T` permutes the cover as it permutes the
vertices of `Δ(A_T)`.

*(c)* By the nerve theorem, `H_{n−1}(Δ(A_T); Z) ≅ H_{n−1}(Y; Z) ≅ ZA_T` as left
`ZA_T`-modules. By `artin-complex-top-homology-is-intersection-of-ideals`, item 2,
`H_{n−1}(Δ(A_T); Z)` is the left ideal `G(A_T) ⊆ ZA_T`. A left ideal isomorphic to `ZA_T` is
`ZA_T·y_T`, where `y_T` is the image of `1`, and `a ↦ a·y_T` is the isomorphism, hence
injective. For `n = 1`, `G(A_{\{s\}}) = ZA·(1 − s)` and `a ↦ a(1 − s)` is injective since `s` has
infinite order. ∎

**Right multiplication stays injective in `ZA`.** Let `A_T ⊆ A` and `R` be representatives of
`A/A_T`. By the unique expansion `a = Σ_r r·a_r` (`a_r ∈ ZA_T`),
`a·y_T = Σ_r r·(a_r y_T)` with `a_r y_T ∈ ZA_T` supported in `A_T`, so `a·y_T = 0` forces every
`a_r y_T = 0`, hence every `a_r = 0`. Also `ZA·y_T = ⊕_r r·ZA_T·y_T`.

**Item 2.** Let `T = S − {u}` and `T' = S − {v}` be spherical, `u ≠ v`.

- `G(A) ⊆ ZA·y_T`: by `artin-ghost-ideal-localizes-to-standard-parabolics`,
  `G(A) ⊆ ⊕_r r·G(A_T) = ⊕_r r·ZA_T·y_T = ZA·y_T`. Likewise `G(A) ⊆ ZA·y_{T'}`.
- `ZA·y_T ∩ ZA·y_{T'} ⊆ G(A)`: `y_T ∈ G(A_T) ⊆ ZA_T·(1 − s)` for every `s ∈ T`, so
  `ZA·y_T ⊆ ZA·(1 − s)` for `s ∈ T`. Likewise for `T'`. Since `T ∪ T' = S`, an element of both
  ideals lies in `ZA·(1 − s)` for every `s ∈ S`.

So `G(A) = ZA·y_T ∩ ZA·y_{T'}`. The map `(a, b) ↦ a·y_T` sends the relation module onto this
intersection, and it is injective: `a·y_T = 0` gives `a = 0` and then `b·y_{T'} = 0` gives
`b = 0`. ∎

**Calibration facts used in the claim.** (i) For finite `W_S`, `x_S` is nonzero and in `G(A)`
(`artin-complex-top-homology-is-intersection-of-ideals`, item 3). (ii) With `m_uv = ∞`, the
standard presentation is the amalgam of `A_T` and `A_{T'}` over `A_{T ∩ T'}`, because every
defining relation involves two generators, and no pair contains both `u` and `v`. The
diagram has an edge labelled `∞`, so `G = 0`. (iii) With `ε: ZA_T → ZW_T`, `ε(G(A_T))` lies in
`⋂_s ZW_T(1 − s) = Z·ν`, `ν = Σ_w (−1)^{ℓ(w)} w` (the coefficients satisfy `a_{ws} = −a_w`).
`ε(x_T) = ν`, `ε(y_T) = kν`, and `gν = (−1)^{ℓ(g)}ν`. So `x_T = c·y_T` gives
`k·Σ_g c_g(−1)^{ℓ(g)} = 1`.
