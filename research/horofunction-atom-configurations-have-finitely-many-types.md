---
rg: 2
id: horofunction-atom-configurations-have-finitely-many-types
kind: claim
title: For a hyperbolic group, tuples of distinct atoms of one level whose boundary images share a Gromov boundary point have finitely many types under simultaneous morphisms; so every fiber product of the horofunction boundary over the Gromov boundary is the boundary of a finite-type tree
requires:
  - horofunction-boundary-homology-reduces-to-the-branch-locus
distinct_from:
  horofunction-boundary-homology-reduces-to-the-branch-locus: that reduces the homological test to the fiber products X^{[p]}_≠ over the branch locus; this proves those fiber products are finite-type coded spaces, the input an Anderson–Putnam argument needs.
---

**ESTABLISHED** (lane proof, bh-finf-hyp, 2026-09-18; not reviewed; no priority claimed).
- The proof applies BBMZ (arXiv:2309.06224) `prop:MakeMorphisms` to tuples. That proposition
  rests on Belk–Bleak–Matucci, Propositions 3.21 and 3.27, and is used here as stated by BBMZ.
- It also uses Cannon's finiteness of cone types and standard thin-triangle estimates.

## Setting

- **The group and its boundaries.** `G` is hyperbolic with finite generating set `S` and
  constant `δ`. `X = ∂_h G`, and `φ : X → ∂G` is the finite-to-one map of Webster–Winchester.
- **Atoms.** `𝒜_n` is the set of infinite atoms of `B_n`, and `∂A` is the shadow of `A`.
  `K_A = φ(∂A)` is a closed subset of `∂G`.
- **Configurations.** A `p`-configuration of level `n` is a tuple `𝐀 = (A_0, …, A_p)` of pairwise
  distinct atoms in `𝒜_n` with `K_{A_0} ∩ ⋯ ∩ K_{A_p} ≠ ∅`.
- **Children.** A child configuration of `𝐀` is a `p`-configuration `(A'_0, …, A'_p)` of level
  `n+1` in which each `A'_i` is a child of `A_i`.
- **Types.** `g ∈ G` is a *morphism* `𝐀 → 𝐀'` if it is a morphism `A_i → A'_i` (BBMZ
  `def:morphisms`) for every `i`. Two configurations related by a morphism have the *same type*.

## Theorem

1. **Bounded spread.** There is `R = R(δ)` with the following property. For every
   `p`-configuration `𝐀` of level `n`, and every `ξ ∈ ∩_i K_{A_i}` with geodesic ray `γ` from `1`
   to `ξ`, every `N(A_i)` lies in the ball `B_R(γ(n))`.
2. **Finitely many types.** For each `p`, the `p`-configurations of all levels have finitely many
   types.
3. **Types are self-similar.** A morphism `𝐀 → 𝐀'` maps the child configurations of `𝐀`
   bijectively onto those of `𝐀'`, and it is a morphism between each pair. So the type of `𝐀`
   determines the multiset of types of its children.
4. **Finite-type coding.**
   - The set `W_n` of `(η_0, …, η_p) ∈ X^{[p]}` whose level-`n` atoms are pairwise distinct is a
     compact open subset of `X^{[p]}_≠`, and `X^{[p]}_≠ = ⋃_n W_n`.
   - `W_n` is the disjoint union, over `p`-configurations `𝐀` of level `n`, of the sets
     `X^{[p]} ∩ (∂A_0 × ⋯ × ∂A_p)`.
   - Each of these sets is homeomorphic to the space of infinite descending paths of
     configurations starting at `𝐀`.
   - So `X^{[p]}_≠` is an increasing union of finite unions of boundaries of trees with finitely
     many vertex types. Configurations of the same type have `G`-translate boundaries.

## Proof

**1.**
- Let `η_i ∈ ∂A_i` with `φ(η_i) = ξ`, and write `η_i = lim d_{x_k}`.
  - Eventually `d_{x_k}` agrees with `d_{A_i}` on `B_n` modulo constants, so `x_k ∈ A_i`.
  - `φ(η_i) = lim x_k` in `G ∪ ∂G`, so `x_k → ξ`.
- `N(A_i) = N(x_k, B_n)` is the set of points where geodesics `[1, x_k]` cross the sphere `S_n`
  (BBMZ, §4.4, description (ii)).
- Since `(x_k | ξ)_1 → ∞`, for large `k` every geodesic `[1, x_k]` stays within `8δ` of `γ` up to
  time `n` (ideal triangles are `2δ`-thin up to a factor 4, a standard estimate). So its point at
  distance `n` from `1` lies within `R = 8δ + 2` of `γ(n)`.
- Diameter bounds are uniform, so one `R` depending only on `δ` works.

**2.** Let the signature of `𝐀` be the data of BBMZ's `prop:MakeMorphisms`, for all `i` at once:
- the sets `N̂(A_i) = S_n ∩ B_{4δ+2}(N(A_i))`;
- the functions `d_{A_i}` on `N̂(A_i)`, modulo constants;
- the cones `C(x)` for `x ∈ ⋃_i N̂(A_i)`.

Call two signatures equivalent if one `ℓ ∈ G` carries the first to the second, coordinate by
coordinate.
- **Equivalent signatures give a morphism.** If `ℓ` carries the signature of `𝐀` to that of
  `𝐀'`, then conditions (i)–(iii) of `prop:MakeMorphisms` hold for each pair `(A_i, A'_i)`. So
  `ℓ` is a morphism `A_i → A'_i` for every `i`, and hence a morphism `𝐀 → 𝐀'`.
- **Finitely many classes.** By item 1, `⋃_i N̂(A_i)` lies in a ball of radius `R + 4δ + 2`
  around `γ(n)`. Translate `γ(n)` to `1`. Then:
  - there are finitely many choices for the sets `N̂(A_i)`, which are subsets of a fixed ball;
  - there are finitely many choices for the functions: `1`-Lipschitz integer functions modulo
    constants on a finite set;
  - there are finitely many choices of cones, by Cannon's finiteness of cone types.

  So there are finitely many classes of signatures, hence finitely many types.

**3.**
- Morphisms restrict to morphisms between child atoms (BBMZ `rem:SelfSimilarTree`, and
  condition (iii) of `def:morphisms`), so `ℓ` maps children to children.
- `φ` is `G`-equivariant and morphisms are group elements. So `K_{ℓA'} = ℓK_{A'}`, and the
  intersection condition is preserved.
- Distinctness is preserved because `ℓ` is a bijection.

**4.**
- **`W_n` is compact open.** Membership in `W_n` depends only on the level-`n` atoms of the
  coordinates. `X^{[p]}` is compact, so `W_n` is compact. Distinct points are separated at some
  level, so the `W_n` exhaust `X^{[p]}_≠`.
- **Paths give points.** A descending path of configurations `𝐀^{(n)} ⊃ 𝐀^{(n+1)} ⊃ ⋯` determines
  `η_i = ⋂_m ∂A_i^{(m)}`. The sets `⋂_i K_{A_i^{(m)}}` are nonempty, compact and nested, so a
  point `ξ` lies in all of them. Then `φ(η_i) ∈ ⋂_m K_{A_i^{(m)}}`. That intersection is the image
  of a nested sequence of shadows shrinking to a point, so it equals `{φ(η_i)}`. Hence
  `φ(η_i) = ξ` for all `i`, and `(η_i) ∈ X^{[p]}`.
- **Points give paths.** Conversely, a point of `X^{[p]} ∩ ∏ ∂A_i` determines its descending path.
- Both correspondences are continuous, so they are homeomorphisms.
- Configurations of the same type are related by a group element `ℓ`, whose diagonal action on
  `X^{p+1}` preserves `X^{[p]}`. `∎`

## Lesson for general BH

- **Configurations are as finite as atoms.** The finiteness of atom types in a hyperbolic group
  (BBM) is not special to single atoms. Any bounded configuration of atoms has finitely many
  types, by the same local-signature argument. The reason is that thin triangles confine
  everything that meets one boundary point to a bounded window.
- **So Cantor models of hyperbolic boundaries are finite-type at every order.** This covers the
  model itself and all its fiber products over `∂G`, which are the strata of its branch locus.
- **What this supplies.** It is the finite-type input that Anderson–Putnam arguments and Thumann
  operads without finite type (`thumann-finiteness-without-finite-type`) consume. What remains
  is the global finiteness argument, not local finiteness data.

## Next

- **Equivariant Anderson–Putnam argument.** Build a finite `G`-CW model for each `W_n`: a
  configuration complex with cells indexed by configuration types. Then show that
  `H^*(G; C_c(X^{[p]}_≠, Q))` is a direct limit of finite-dimensional groups under the refinement
  maps.
- **The obstacle.** Unlike a substitution tiling, `G` does not act on the levels. The atom tree is
  not `G`-invariant, so the direct limit must be formed through the structured atom set
  `{(g, A)}/morphisms`, on which `G` does act.
