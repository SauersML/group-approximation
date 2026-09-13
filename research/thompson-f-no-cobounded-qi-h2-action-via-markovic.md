---
rg: 2
id: thompson-f-no-cobounded-qi-h2-action-via-markovic
kind: route
title: Markovic rigidity plus simplicity of [F,F] rule out cobounded F-actions on spaces quasi-isometric to H^2
target: thompson-f-has-no-cobounded-action-on-spaces-qi-to-h2
requires:
  - uniformly-quasisymmetric-circle-groups-are-mobius-conjugates
  - h2-quasi-isometries-have-uniformly-quasisymmetric-boundary-maps
  - thompson-f-has-no-free-subgroups
  - abelian-isometry-groups-of-h2-are-not-cobounded
---

Suppose `F` acts isometrically and coboundedly on a geodesic space `X`, and `φ: X → H^2` is
a quasi-isometry with quasi-inverse `ψ`. Then `g ↦ f_g = φ∘g∘ψ` is a cobounded quasi-action
of `F` on `H^2` by `(K,C)`-quasi-isometries with uniform constants. Let `∂: F → Homeo(S^1)`
be the boundary homomorphism (`h2-quasi-isometries-have-uniformly-quasisymmetric-boundary-maps`),
`N = ker ∂`, a normal subgroup. Classical inputs used in the body: stability of
quasi-geodesics in `H^2` (Bridson–Haefliger, III.H.1.7, not re-read) and Gromov's
classification of isometric actions on hyperbolic spaces.

**(A) Elements of `N` are uniformly close to the identity.** Every `x ∈ H^2` lies within a
universal distance `r_0` of all three sides of some ideal triangle `Δ`. If `∂f = id`, then
`f` maps each side to a `(K,C)`-quasi-geodesic with the same endpoints, which lies within
`M(K,C)` of that side. So `f(x)` is within `K r_0 + C + M` of all three sides of `Δ`, and
the set of such points has diameter at most `D_0(K,C)`, while `x` itself belongs to it.
Hence `d(f(x), x) ≤ D_0`.

**(B) Simplicity dichotomy.** `[F,F]` is simple (Dudko–Medynets, quoted in
`thompson-f-has-no-cobounded-action-on-hyperbolic-plane-proof`), so `N ∩ [F,F]` is `1` or
`[F,F]`.

**(C) Case `[F,F] ∩ N = 1`.** `[F,F]` has no index-2 subgroup (it is simple and infinite),
so it lies in the orientation-preserving subgroup `F^+ = ∂^{-1}(Homeo^+(S^1))`, which has
index at most 2, is finitely generated, and contains `N`. The group `∂(F^+)` is uniformly
quasisymmetric, so by `uniformly-quasisymmetric-circle-groups-are-mobius-conjugates` it is
isomorphic to a subgroup of `PSL_2(R)`: a finitely generated linear group. It has no
non-abelian free subgroup, since free subgroups lift to `F`
(`thompson-f-has-no-free-subgroups`), so by the Tits alternative it is virtually solvable.
But `[F,F]` embeds in it, contradicting Step 2 of the literal-reading proof: an infinite
non-abelian simple group is not virtually solvable.

**(D) Case `[F,F] ≤ N`.** The action on `X` is cobounded and `X` is unbounded, so its limit
set is all of `∂X ≅ S^1`. Hence it is neither elliptic, horocyclic nor lineal, and by
Gromov's classification some `g ∈ F` is loxodromic. Its transported quasi-isometry `f_g`
fixes two boundary points `g^±` and quasi-preserves the geodesic `ℓ` joining them. Since
`F/N` is abelian, every `∂h` commutes with `∂g`, so it preserves `{g^+, g^-}`; the subgroup
`B` fixing both points has index at most 2. Each `f_h` with `h ∈ B` maps `ℓ` to a
quasi-geodesic with the same endpoints, within `M(K,C)` of `ℓ`. So for `x ∈ ℓ`,
`B·x ⊆ N_{M}(ℓ)` up to the uniform quasi-action error, and `F·x` lies within bounded
distance of `ℓ ∪ f_σ(ℓ)` for one `σ ∉ B`. Two quasi-geodesics are not coarsely dense in
`H^2`: contradiction. (Here only (A) and quasi-geodesic stability are used; the lemma
`abelian-isometry-groups-of-h2-are-not-cobounded` is its isometric special case.)

Both cases are impossible, so no such action exists. ∎

Status: the route is complete modulo its two open import claims, whose sources must be read
verbatim; nothing else is conditional.
