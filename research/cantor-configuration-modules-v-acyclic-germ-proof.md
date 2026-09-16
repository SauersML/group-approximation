---
rg: 2
id: cantor-configuration-modules-v-acyclic-germ-proof
kind: route
title: Pass from the transformation groupoid to the germ groupoid through the Leray spectral sequence, then restrict a power of the full 2-shift groupoid
target: cantor-configuration-function-modules-are-v-acyclic
requires:
  - crainic-moerdijk-groupoid-leray-spectral-sequence
  - matui-groupoid-homology-transformation-and-reduction
  - matui-groupoid-homology-kunneth-and-full-shift-vanishing
  - thompson-v-is-integrally-acyclic
artifacts:
  - research/artifacts/cantor-configuration-modules-v-acyclic-germ-groupoid-2026-09-16.md
---

Full proof: artifact, Sections 1–4 (Theorem 1). Fix `m >= 1` and put `X = Conf_m(C)`.

1. **Group to groupoid.** `H_p(V; C_c(X, Z)) ≅ H_p(X ⋊ V; Z)`
   (`matui-groupoid-homology-transformation-and-reduction`, item 1).
2. **The germ groupoid is the full 2-shift groupoid (Lemma 1.1).** Let `𝒱` be the germ
   groupoid of `V` on `C`. The map `[g]_y ↦ (g(y), |v| − |u|, y)` is an isomorphism
   `𝒱 ≅ G_2` of étale groupoids, where `g = τ_{v,u}` near `y`. Surjectivity uses that
   when `uC` and `vC` are proper cones, some element of `V` extends `τ_{v,u}`.
3. **Restriction (Lemma 2.1, Proposition 2.2).** Let `𝒢 = 𝒱^m|X`.
   - `X` is open and `𝒱^m`-full: move any tuple onto distinct points by distinct
     prefixes.
   - By reduction (item 2 of the Matui node), `H_*(𝒢) ≅ H_*(𝒱^m) ≅ H_*(G_2^m)`.
   - `H_*(G_2^m) = 0` by Künneth and `H_*(G_2) = 0`
     (`matui-groupoid-homology-kunneth-and-full-shift-vanishing`).
4. **Comparison homomorphism.** `φ : X ⋊ V → 𝒢`, `(g, x) ↦ ([g]_{x_i})_i`. It is an
   étale homomorphism with `φ_0 = id`.
5. **Comma groupoids (Lemmas 3.1–3.3).**
   - `x/φ` is discrete, because its object space is a source fibre of the étale `𝒢`.
   - `x/φ` is connected: any tuple of germs between two configurations is realized by
     one `g ∈ V`.
   - Its isotropy is `K_x = {h : h = id near every x_i}`. This group is the directed
     union of the subgroups fixing a proper clopen neighbourhood of the `x_i`, each
     isomorphic to `V`. So `H_q(x/φ; Z) = H_q(K_x; Z) = 0` for `q >= 1`
     (`thompson-v-is-integrally-acyclic`).
6. **Collapse (Proposition 3.4).** In the spectral sequence
   `H_p(𝒢; L_qφ_!Z) ⇒ H_{p+q}(X ⋊ V; Z)` (`crainic-moerdijk-groupoid-leray-spectral-sequence`):
   - the stalks give `L_qφ_!Z = 0` for `q >= 1`;
   - `L_0φ_!Z = coker(B_1 → s_!Z)`, and summation along `s` identifies it with the
     constant `𝒢`-sheaf `Z`, since every `x/φ` is connected.
   - So `H_p(X ⋊ V; Z) ≅ H_p(𝒢; Z) = 0`.

Referee targets are listed in artifact Section 7.
- The identification `L_0φ_!Z ≅ Z` as a `𝒢`-sheaf.
- Discreteness of `x/φ`.
- The standing hypotheses of Crainic–Moerdijk, all of which hold because every space is
  second countable, locally compact, Hausdorff and zero-dimensional.

Sanity checks are in artifact Section 6.
- Degree 0 agrees with the subdivision argument.
- Degrees 0 and 1 for `m = 1` agree with Palmer–Wu acyclicity of `V(Z)`.
- The rational case agrees with Lemma C5 of part 3.
