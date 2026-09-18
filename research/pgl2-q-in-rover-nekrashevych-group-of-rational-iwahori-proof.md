---
rg: 2
id: pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori-proof
kind: route
title: Mobius maps are similarities on small p-adic balls, so PGL_2(Q) is piecewise Gamma_p on P^1(Q_p)
target: pgl2-q-in-rover-nekrashevych-group-of-rational-iwahori
requires: []
---

Direct proof. Notation as in the target; `|.|` is `|.|_p`.

**Lemma (similarity).** Let `g(z) = (αz+β)/(cz+δ) ∈ PGL_2(Q_p)`. For
`x, y ≠ -δ/c`,
`g(x) - g(y) = (αδ - βc)(x - y) / ((cx+δ)(cy+δ))`.
Let `B` be a ball of radius `r` around `z_0`, with `r < |z_0 + δ/c|` (any `r` if
`c = 0`). Then `|cx + δ| = |c z_0 + δ|` on `B`, by the ultrametric inequality. So
`|g(x) - g(y)| = ρ|x - y|` on `B`, with `ρ = |αδ - βc| / |c z_0 + δ|^2`, an
integral power of `p`. Shrinking `B` so that the same holds for `g^{-1}` on the
ball of radius `ρr` around `g(z_0)`, one gets that `g` maps `B` bijectively onto
that ball.

**Item 1.** `γ ∈ Γ_p` is a bijective isometry of `Z_p`, so
`γ(a + p^k Z_p) = b + p^k Z_p` for a unique canonical `b`. The section
`σ = φ_{b,k}^{-1} ∘ γ ∘ φ_{a,k}` is a composite of rational Möbius maps, so
`σ ∈ PGL_2(Q)`. It maps `Z_p` onto `Z_p`, and it scales distances by
`p^k · 1 · p^{-k} = 1`. So `σ ∈ Γ_p`.

The sections at the level-1 cones give the wreath recursion
`γ = π(γ_0, ..., γ_{p-1})` with `γ_i ∈ Γ_p`, which is Zaremsky's definition of
self-similarity (quoted in `fp-self-similar-groups-embed-in-fp-simple-groups-citation`).

**Item 2.**
- *Iwahori matrices are in `Γ_p`.* Take `[[α,β],[c,δ]] ∈ GL_2(Z_(p))` with
  `c ∈ pZ_(p)`. Its determinant is a unit and `c ≡ 0 (mod p)`, so `α` and `δ`
  are units. For `x ∈ Z_p`, `|cx + δ| = 1`. So the map sends `Z_p` into `Z_p`
  and, by the Lemma with `ρ = 1`, is an isometry. Its inverse matrix has the same
  form, so the map is onto.
- *Conversely.* Take `γ = (αz+β)/(cz+δ)` in `Γ_p` with no pole on `Z_p`. The
  Lemma gives `|cx + δ|^2 = |det|` for all `x ∈ Z_p`.
  - If `|c| > |δ|`, then `x = 0` and `x = 1` give different values.
  - If `|c| = |δ| ≠ 0`, choose `x ∈ Z_p` with `|x + δ/c| < 1`, which is possible
    since `δ/c` is a unit. Then `|cx + δ| < |δ|`.
  - Hence `|c| < |δ|`. Scale so that `δ = 1`. Then `c ∈ pZ_p`,
    `|det| = |cx + δ|^2 = 1`, and `β = γ(0) ∈ Z_p`. Also
    `α = det + βc ∈ Z_p`.
  - The entries are rational, so they lie in `Q ∩ Z_p = Z_(p)`, and
    `det ∈ Z_(p)^×`.

**Item 3.** The group `PGL_2(Q_p)` acts faithfully on `P^1(Q_p)`, and
`PGL_2(Q) -> PGL_2(Q_p)` is injective. Write `X = P^1(Q_p) = Z_p ⊔ D_∞`.
The chart `φ_∞(u) = 1/(pu)` is a homeomorphism `Z_p -> D_∞`: `|1/(pu)| = p/|u| >= p`,
and `z ↦ 1/(pz)` inverts it. Both charts are rational Möbius maps.

Call a subset of `X` a *cone* if it is `φ_s(a + p^k Z_p)` for a chart `s ∈ {0, ∞}`
and some `k >= 0`, and give it the coordinate `φ_s ∘ φ_{a,k}`. This makes `X`
the end space of two `p`-ary rooted trees. Let `V_{p,2}(Γ_p)` be the group of
homeomorphisms of `X` that are piecewise `(coordinate) ∘ γ ∘ (coordinate)^{-1}`,
with `γ ∈ Γ_p`, on a finite cone partition.

*Every `g ∈ PGL_2(Q)` lies in `V_{p,2}(Γ_p)`.* Fix `x ∈ X`. Choose charts `s`
with `x ∈ φ_s(Z_p)` and `t` with `g(x) ∈ φ_t(Z_p)`. The map
`F = φ_t^{-1} ∘ g ∘ φ_s` is a rational Möbius map, defined and continuous at
`u_0 = φ_s^{-1}(x)`. By the Lemma and continuity, there is a ball
`u_0 + p^k Z_p` with `k >= 0` such that:
- `F` has no pole there;
- `F` maps it by a similarity onto a ball `b + p^{k'} Z_p ⊆ Z_p` with `k' >= 0`.

Such balls are cones, and any two cones are nested or disjoint. Compactness of
`X` gives finitely many of them covering `X`, and the maximal ones form a
partition. On a piece with coordinate `φ_s ∘ φ_{a,k}` and image coordinate
`φ_t ∘ φ_{b,k'}`, the normalized map
`γ = φ_{b,k'}^{-1} ∘ F ∘ φ_{a,k}` is a rational Möbius similarity of `Z_p` onto
`Z_p`. Both sets have diameter 1, so the ratio is 1, and `γ ∈ Γ_p`. The image
cones partition `X` because `g` is a bijection. So `g ∈ V_{p,2}(Γ_p)`, and
`PGL_2(Q) -> V_{p,2}(Γ_p)` is an injective homomorphism.

*`V_{p,2}(Γ_p)` embeds in `V_p(Γ_p)`.* Let `Θ : X -> 0 + pZ_p ⊔ 1 + pZ_p` send
`φ_0(u) ↦ pu` and `φ_∞(u) ↦ 1 + pu`. Then
`Θ(φ_0(a + p^k u)) = φ_{pa,k+1}(u)` and `Θ(φ_∞(a + p^k u)) = φ_{1+pa,k+1}(u)`,
with canonical representatives. So `Θ` carries cones to cones and coordinates to
coordinates. Conjugating by `Θ`, and extending by the identity on the cones
`c + pZ_p` with `2 <= c <= p-1` (there are none for `p = 2`), gives an injective
homomorphism `V_{p,2}(Γ_p) -> V_p(Γ_p)`.

The translations `z ↦ z + q`, `q ∈ Q`, form a copy of `(Q,+)` in `PGL_2(Q)`.

**Item 4.**
- *Not finitely generated.* A finitely generated subgroup of `PGL_2(Q)` is
  represented by matrices with entries in `Z[1/N]` for some `N`. For a prime
  `q ∤ Np`, the translation by `1/q` lies in `Γ_p`. It has no such
  representative: `λ[[1,1/q],[0,1]]` with `λ, λ/q ∈ Z[1/N]` and `λ^2 ∈ Z[1/N]^×`
  is impossible.
- *Not finite-state.* `γ(u) = u/(1+pu)`, the class of `[[1,0],[p,1]]`, lies in
  `Γ_p` by Item 2. From the Lemma,
  `γ(a + p^k v) = γ(a) + p^k v / ((1+pa)(1+pa+p^{k+1} v))`.
  So its section at the cone `(a, k)` is `v ↦ c_{a,k} + v / ((1+pa)(1+pa+p^{k+1}v))`,
  whose pole is `v = -(1+pa)/p^{k+1}`. Distinct pairs `(a, k)` give distinct
  poles, hence distinct Möbius maps, hence (agreeing nowhere on an infinite set)
  distinct sections. There are infinitely many.
- *No contracting overgroup.* In a contracting group every element has finitely
  many sections: finitely many vertices lie above the level where all sections
  enter the finite nucleus. So no contracting self-similar group contains `Γ_p`.

**Item 5(a).** Let `ψ : SL_2(Q) -> PGL_2(K)` be a homomorphism with
`t = ψ(-I) ≠ 1`.
- *`ψ` is injective.* `PSL_2(Q)` is simple and `SL_2(Q)` is perfect. So the
  normal subgroups of `SL_2(Q)` are `1`, `{±I}` and `SL_2(Q)`, and `ker ψ`
  contains none but `1`.
- *The centralizer of `t` is virtually abelian.* Write `t = [A]` with `A^2 = λI`
  and `A` not scalar. If `[g]` commutes with `t`, then `gAg^{-1} = μA`, so
  `μ^2 = 1`. The classes with `μ = 1` form `K[A]^× / K^×`. Here `K[A]` is a
  commutative 2-dimensional algebra, so this is an abelian subgroup of index at
  most 2 in the centralizer.
- *Contradiction.* `ψ(SL_2(Q))` centralizes `t`, so `SL_2(Q)` would be virtually
  abelian. It is not, since `[[1,2],[0,1]]` and `[[1,0],[2,1]]` generate a free
  group.

Hence `-I` dies in every factor of a product of groups `PGL_2(K_j)`.

**Item 5(b).** Take the affine chart `x_1 = 1` of `P^{n-1}(Q_p)`. The metric on
the polydisc `Z_p^{n-1}` is the max-norm, and its balls are
`y + p^k Z_p^{n-1}`.
- `g = diag(1, ..., 1, p)` acts there as
  `(y_2, ..., y_n) ↦ (y_2, ..., y_{n-1}, p y_n)`.
- For `n >= 3` there is at least one unscaled coordinate. So the image of every
  ball `y + p^k Z_p^{n-1}` is `(y' + p^k Z_p^{n-2}) × (p y_n + p^{k+1} Z_p)`. It
  contains points at distance `p^{-k}` but none at that distance in the last
  coordinate, so it is not a ball.
- An almost automorphism maps some cone around each point onto a cone. So `g`
  is not an almost automorphism of the tree of balls.
