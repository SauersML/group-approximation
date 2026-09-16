---
rg: 2
id: planar-rips-complexes-have-free-first-homology-proof
kind: route
title: "Proof: pass to shadows, read first homology off winding numbers, and embed the colimit in continuous functions on a profinite space"
target: planar-rips-complexes-have-free-first-homology
requires:
  - planar-rips-projection-is-a-pi1-isomorphism
  - profinite-integer-function-groups-are-free
artifacts:
  - research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md
---

Full details are in §2 (A1–A6) of
`research/artifacts/zaremsky-4-02-planar-rips-infinite-2026-09-16.md`. Write
`R(Y) = R_r(Y)` in the chosen convention.

**Step 1: colimit.** Compact subsets of `|R(X)|` lie in finite subcomplexes,
and each finite subcomplex lies in `R(F)` for some finite `F ⊆ X`. So
`H_1(R(X)) = colim_F H_1(R(F))` over the directed set of finite `F ⊆ X`.

**Step 2: shadows.**

- Let `p_F : |R(F)| → R^2` be the affine extension of `F ⊆ R^2`, with image the
  shadow `S(F)`. `S(F)` is a finite union of points, segments and triangles.
- By `planar-rips-projection-is-a-pi1-isomorphism`, `p_F` is a bijection on
  `π_0` and an isomorphism on each `π_1`. Finite sets are covered in both
  conventions.
- By Hurewicz on each component, `p_{F*}` is an isomorphism on `H_1`.
- For `F ⊆ F′`, `p_{F′}` restricts to `p_F` on the full subcomplex `R(F)`. So
  `H_1(R(X)) ≅ colim_F H_1(S(F))`, with maps induced by the inclusions
  `S(F) ⊆ S(F′)`.

**Step 3: winding numbers.** Let `K ⊆ R^2` be a compact polyhedron and `W(K)`
the set of bounded components of `R^2 ∖ K`. Winding numbers around one point
`p_U` in each `U ∈ W(K)` give `ω_K : H_1(K) → Z^{W(K)}`.

*`ω_K` is an isomorphism.* Triangulate a closed triangle `D` with
`K ⊆ int D` so that `K` is a subcomplex (artifact A3 gives an explicit
construction).

- *Injective.* If `ω_K[c] = 0`, write `c = ∂σ` in `D`. Winding around an
  interior point of a triangle `t` gives the coefficient `σ_t`. For `t ∉ K` that
  point lies in a bounded component, where the winding is `0` by hypothesis, or
  in the unbounded one, where it is `0` anyway. So `σ` is a chain of `K`.
- *Surjective.* `∂(Σ_{int t ⊆ U} t)` is a cycle of `K`. Interior edges outside
  `K` cancel, and boundary edges of `D` border the unbounded component. Its
  winding vector is the basis vector `e_U`.

*Naturality.* For `K ⊆ L`, send each `V ∈ W(L)` to the component of
`R^2 ∖ K` containing it, or to `∞` if that component is unbounded. This gives
`π : W(L) ⊔ {∞} → W(K) ⊔ {∞}`, and `ω_L ∘ incl_* = π^* ∘ ω_K`. Here elements of
`Z^{W(K)}` are the pointed maps `W(K) ⊔ {∞} → Z` that vanish at `∞`.

**Step 4: profinite embedding.**

- Put `P(F) = W(S(F)) ⊔ {∞}`. By Steps 1–3,
  `H_1(R(X)) ≅ colim_F Z_0^{P(F)}`, with transitions `π^*`.
- `Ω = lim_F P(F)` is profinite. `Φ[f] = f ∘ pr_F` is a well-defined
  homomorphism into `C(Ω, Z)`.
- `Φ` is injective. Suppose `f ∘ pr_F = 0`. Choose `F* ⊇ F` where the image of
  `P(F*)` in `P(F)` is smallest. That image is then stable for all `F′ ⊇ F*`.
- Every point `a` of the stable image lifts to `Ω`. The fibres over `a` form an
  inverse system of nonempty finite sets over a directed set, and such a
  system has nonempty limit by compactness.
- So `f` vanishes on the stable image, `π_{FF*}^* f = 0`, and `[f] = 0`.

**Step 5: freeness.**

- By `profinite-integer-function-groups-are-free` (Nöbeling's theorem),
  `C(Ω, Z)` is free abelian.
- Subgroups of free abelian groups are free.
- So `H_1(R(X))` is free. ∎

For countable `X` the citation can be avoided.

- Take an exhaustion `F_1 ⊆ F_2 ⊆ …` and put `Ω_n = pr_{F_n}(Ω)`.
- `C(Ω, Z)` is the increasing union of the finitely generated subgroups
  `pr_{F_n}^* Z^{Ω_n}`. A locally constant function on the compact space `Ω`
  factors through some `pr_{F_n}`.
- Each of these subgroups is pure, because `pr_{F_n}` maps onto `Ω_n`.
- Lemma C of the artifact (§5) then gives freeness of `C(Ω, Z)` directly, so
  for countable `X` the second prerequisite is not needed.
