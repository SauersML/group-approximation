---
rg: 2
id: f-dyadic-order-preserving-wobbles-locally-f-proof
kind: route
title: Extend order-preserving wobbles to dyadic-affine maps with rational breakpoints, filter by the odd part of breakpoint denominators, rescale by odd M and re-tile into F while keeping D inside D, and push invariant means through restriction, conjugacy and directed unions
target: f-dyadic-order-preserving-wobbles-are-locally-f
requires:
  - f-dyadic-orbit-geometry-cannot-force-extensive-amenability
  - affine-lamplighter-amenable-iff-extensively-amenable
  - thompson-f-amenable-iff-dyadic-action-extensively-amenable
  - f-dyadic-ea-iff-inverted-orbit-confinement
  - pl-plus-interval-has-no-non-abelian-free-subgroups
---

**Imports.**
- (J1) JMBMdlS Definition 1.1, quoted verbatim in `affine-lamplighter-amenable-iff-extensively-amenable-citation`
  (and restated in `f-dyadic-orbit-geometry-cannot-force-ea-proof`): "The action of a group G on a set X is
  extensively amenable if there is a G-invariant mean on P_f(X) giving full weight to the collection of
  subsets that contain any given element of P_f(X)."
- (J2) JMBMdlS Lemma 2.1, same place: "Every action of an amenable group is extensively amenable, and every
  extensively amenable action on a nonempty set is amenable."
- (W7) Step 7 of `f-dyadic-orbit-geometry-cannot-force-ea-proof`. For `h ∈ W^+(Γ_D)` there is a finite
  `B ⊆ F` such that the unique increasing extension `Ĥ` of `h` to `[0,1]` agrees with a single element of `B`
  on each of the finitely many components of `[0,1] ∖ Z`. Here `Z` is finite, and `h ↦ Ĥ` is an injective
  homomorphism.
- (E) `thompson-f-amenable-iff-dyadic-action-extensively-amenable`, item 1: `F` is amenable iff `F ↷ D` is EA.
- (C) `f-dyadic-ea-iff-inverted-orbit-confinement`: `F ↷ D` is EA iff the hole
  `f-dyadic-inverted-orbit-is-subballistic-on-rare-events` holds.
- (A) `F ↷ D` is amenable. This follows from `f-dyadic-orbit-geometry-cannot-force-extensive-amenability`,
  item 3(a): `G ↷ D` is amenable with Følner sets for a generating set of `G ⊇ {x_0, x_1}`, and the same
  sets are Følner for `F`. It also follows from (E) for amenable `F`. It is used only in part 5.
- (BS) `pl-plus-interval-has-no-non-abelian-free-subgroups`.

**Part 1.**
- `F ≤ W^+(Γ_D)`: an element `f ∈ F` moves each point by at most `|f|_S` in `Γ_D`, and it is increasing.
- Let `h ∈ W^+(Γ_D)`. By (W7), `Ĥ` is a homeomorphism of `[0,1]` that equals one element `g_J ∈ F` on each
  component `J` of `[0,1] ∖ Z`, and there are finitely many components.
- Each `g_J` is piecewise `x ↦ 2^k x + d` with `k ∈ Z` and `d ∈ Z[1/2]`, with finitely many pieces. Its
  pieces are between dyadic breakpoints, where `d = g(a) − 2^k a` is dyadic.
- So `Ĥ` has finitely many pieces of this form, and `Ĥ ∈ Q_2`. Hence `W^+(Γ_D) ≤ Q_2`, through the
  injective homomorphism of (W7).

**Part 2.**
- Call a map `x ↦ 2^k x + d` with `k ∈ Z` and `d ∈ Z[1/2]` *dyadic-affine*. Dyadic-affine maps form a
  group, and each one maps `A_M` bijectively onto `A_M`: `2^k (a/M) + d = (2^k a + dM)/M`.
- Let `g, h ∈ Q_2^M`.
  - The breakpoints of `g ∘ h` lie in `bp(h) ∪ h^{-1}(bp(g))`.
  - The breakpoints of `g^{-1}` are `g(bp(g))`.
  - `g` and `h^{-1}` are continuous and piecewise dyadic-affine, so both preserve `A_M`. This holds at
    breakpoints too, since the value there is that of an adjacent piece.
  - So `Q_2^M` is a subgroup.
- `Q_2^1 = F`, by the definition of `F` and the dyadic translation parts found in Part 1.
- If `M | M'`, then `A_M ⊆ A_{M'}`.
- A rational `a/(2^j m)` with `m` odd lies in `A_m`, and breakpoints of elements of `Q_2` are rational. So
  a finitely generated `H ≤ Q_2` lies in `Q_2^M`, where `M` is the lcm of the odd parts of the breakpoint
  denominators of its generators.

**Part 3.** Fix odd `M`.
- **Rescaling.** Let `σ(x) = Mx : [0,1] → [0,M]`. For `g ∈ Q_2^M`, `g' = σ g σ^{-1}` satisfies
  `g'(y) = M g(y/M)`.
  - A piece `2^k x + d` of `g` becomes the piece `2^k y + Md` of `g'`. This is dyadic-affine, since `M` is
    an integer.
  - `bp(g') = M·bp(g) ⊆ M·A_M = Z[1/2]`.
- **Re-tiling.** Choose a finite binary tree with `M` leaves, for example the one of depth `⌈log_2 M⌉`
  with leaves merged as needed. Its leaves are standard dyadic intervals
  `L_j = [a_j, a_j + 2^{-k_j}]`, for `j = 0, …, M − 1` from left to right, and they tile `[0,1]`.
  - Put `τ(y) = a_j + 2^{-k_j}(y − j)` on `[j, j+1]`.
  - `τ` is an increasing homeomorphism `[0,M] → [0,1]` with dyadic-affine pieces and breakpoints at the
    integers `1, …, M−1`, whose images `a_j` are dyadic.
  - Each piece and its inverse map dyadics to dyadics. So `τ(Z[1/2] ∩ [0,M]) = Z[1/2] ∩ [0,1]` and
    `τ((0,M)) = (0,1)`.
- **Into `F`.** Put `θ = τσ`, so `θgθ^{-1} = τ g' τ^{-1}`.
  - Its pieces are composites of dyadic-affine maps, so its slopes lie in `2^Z`.
  - Its breakpoints lie in `bp(τ^{-1}) ∪ τ(bp(g')) ∪ τ(g'^{-1}(bp(τ)))`.
  - The first set is `{a_1, …, a_{M−1}}`. The second is `τ` of dyadics. For the third, `g'^{-1}` has
    dyadic-affine pieces and dyadic breakpoints, so it maps the integers to dyadics. All three sets are
    dyadic.
  - So `θ Q_2^M θ^{-1} ≤ F`.
- **The orbit.** `θ(D) = τ(M·D)`. Since `M·D ⊆ Z[1/2] ∩ (0,M)`, this gives `θ(D) ⊆ D`.
- **Free subgroups and amenability.** `Q_2 ≤ PL_+([0,1])`, so (BS) excludes non-abelian free subgroups.
  - (⇐) If `F` is amenable, each finitely generated `H ≤ Q_2` lies in some `Q_2^M` and is isomorphic to
    `θHθ^{-1} ≤ F`, so it is amenable. Amenability is determined by finitely generated subgroups.
  - (⇒) `F ≤ Q_2`.

**Part 4.** Four facts follow directly from (J1). A mean *good for `(G, X)`* is a `G`-invariant mean on
`P_f(X)` giving full weight to every `U_E = {A : E ⊆ A}` with `E ∈ P_f(X)`.
- (a) **Subgroups.** A mean good for `(G, X)` is good for `(H, X)` when `H ≤ G`.
- (b) **Invariant subsets.** Let `Y ⊆ X` be `G`-invariant, and let `ρ(A) = A ∩ Y`, a `G`-equivariant map
  `P_f(X) → P_f(Y)`. If `m` is good for `(G, X)`, then `ρ_* m`, defined by `(ρ_* m)(φ) = m(φ ∘ ρ)`, is
  `G`-invariant. It is good because `ρ^{-1}(U_E^Y) = U_E^X` for `E ⊆ Y`.
- (c) **Conjugacy.** If `θ : Y → Y'` is a bijection intertwining `H ↷ Y` with `θHθ^{-1} ↷ Y'`, then
  transport of means preserves goodness.
- (d) **Directed unions.** Let `G = ⋃_i G_i` be directed, and let `K_i` be the set of means good for
  `(G_i, X)`.
  - Each `K_i` is weak*-closed in the compact space of means, since `m(γφ) = m(φ)` and `m(1_{U_E}) = 1`
    are closed conditions.
  - Each `K_i` is nonempty by assumption, and the `K_i` decrease along the directed system.
  - So `⋂_i K_i ≠ ∅`, and any element of it is good for `(G, X)`.

Now suppose `F ↷ D` is EA, let `H ≤ Q_2`, and let `Y ⊆ D` be `H`-invariant. Take a finitely generated
`H_0 ≤ H`.
- Then `H_0 ≤ Q_2^M` for some odd `M` (Part 2), and `H_0' = θH_0θ^{-1} ≤ F` (Part 3).
- By (a), `H_0' ↷ D` is EA.
- `θ(Y) ⊆ θ(D) ⊆ D` is `H_0'`-invariant, so `H_0' ↷ θ(Y)` is EA by (b).
- By (c), `H_0 ↷ Y` is EA.
- `H` is the directed union of its finitely generated subgroups, so `H ↷ Y` is EA by (d).

The chain of equivalences:
- `F` amenable ⇔ `F ↷ D` EA, by (E);
- `F ↷ D` EA ⇒ `Q_2 ↷ D` EA, just shown;
- `Q_2 ↷ D` EA ⇒ `W^+(Γ_D) ↷ D` EA ⇒ `F ↷ D` EA, by (a) and Part 1;
- `F ↷ D` EA ⇔ the hole, by (C).

**Part 5.**
- (⇒) Let `H ≤ Q_2` act amenably on `D`, not extensively amenably. By Part 4 `F ↷ D` is not EA, so `F` is
  nonamenable by (E).
- (⇐) If `F` is nonamenable, then `F ≤ W^+(Γ_D)` acts amenably on `D` by (A), and not EA by (E). ∎

**What this does not do.** It proves no instance of the hole. It shows that order preservation together
with `Γ_D`-bounded displacement defines no world strictly between `F` and the wobbling calibrator of
`f-dyadic-orbit-geometry-cannot-force-extensive-amenability`: with order, the world collapses back to `F`.
