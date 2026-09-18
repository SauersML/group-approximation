---
rg: 2
id: degree-coboundary-subgroups-of-coded-full-groups-are-rf
kind: claim
title: In the full group of a finitely coded groupoid, a finitely generated subgroup whose degree cocycle is a continuous coboundary is virtually a subgroup of a finite product of unit groups; so an infinite simple or non-residually-finite input must change level without bound along every orbit
distinct_from:
  finitely-coded-unit-groups-act-residually-finitely: that is the unit groups themselves, whose degree cocycle is zero on one cylinder; this is every finitely generated subgroup whose degree cocycle is a continuous coboundary, bounded by the unit groups up to finite index.
  brin-thompson-torsion-has-clopen-fixed-sets: its item 4 proves that a coboundary forces finiteness in nV, which has finite units and full shifts; this is the same implication for every finitely coded groupoid, with finiteness replaced by "virtually inside a finite product of unit groups".
  periodic-k-graph-subgroups-with-ray-cocycle-are-finite: that gets finiteness of periodic subgroups from a cocycle confined to a ray, by pumping; this assumes a coboundary instead, no periodicity, and needs no pumping.
  finitely-coded-cantor-actions-give-type-a-hosts: that is the positive host machine; this says which inputs its degree-zero part can carry, namely only unit-like ones.
---

**ESTABLISHED.** Lane proof, elementary. Not independently reviewed; no priority claimed.

## Setting

This is the setting of `finitely-coded-unit-groups-act-residually-finitely`, stated with right unit cosets.
- `ℭ` is a left cancellative small category with finitely many objects and a degree map `d : ℭ → N^k`.
  - It satisfies (UFP*).
  - Its invertibles are exactly the morphisms of degree 0.
  - Finitely many morphisms of each degree end at each object, counted modulo right units.
- Cylinders are `Z(x) = x·∂Ω(s(x)) ⊆ ∂Ω(t(x))`, and `η ↦ xη` is a homeomorphism onto `Z(x)`.
- The boundaries are *path-like*:
  - (P1) for `ζ ∈ ∂Ω(v)` and `p ∈ N^k`, the degree-`p` morphisms `x` ending at `v` with `ζ ∈ Z(x)` form exactly one right coset `xℭ*`;
  - (P2) `ζ` is the intersection of these cylinders over all `p`.
  - This holds for `k`-graphs, their Zappa–Szép products, and the orbit categories of building and tree lattices, where the degree-`p` prefix of a sector is its box of shape `p`, modulo the tile stabilizer.
- `Z` is a nonempty clopen subset of the unit space `⊔_v ∂Ω(v)`, that is, a finite union of cylinders. This
  covers reductions to unions of object boundaries and Kakutani reductions.
- `𝒢` is Li's boundary groupoid reduced to `Z`. It is assumed effective, so `F(𝒢) ≤ Homeo(Z)`. Without
  effectiveness, everything below applies to the image of `F(𝒢)` in `Homeo(Z)`.
- The *degree cocycle* `c(γ, z) ∈ Z^k` is `d(y) − d(x)` when `γ` acts near `z` by `xη ↦ yη`. It is locally constant, and `c(γδ, z) = c(γ, δz) + c(δ, z)`.
- `Ū_v` is the image of `ℭ*(v, v)` in `Homeo(∂Ω(v))`. It is residually finite by `finitely-coded-unit-groups-act-residually-finitely`.

## Statement

Let `Γ ≤ F(𝒢)` be finitely generated, and let `Y ⊆ Z` be closed and `Γ`-invariant (for example `Y = Z`).
1. **Scaling-free subgroups are unit-like.** Suppose there is a continuous `b : Y → Z^k` with
   `c(γ, z) = b(γz) − b(z)` for all `γ ∈ Γ` and `z ∈ Y`.
   - (a) The image `Γ_Y` of `Γ` in `Homeo(Y)` is residually finite.
   - (b) If `Y = Z`, then `Γ` has a finite-index subgroup that embeds in a finite product `∏_i Ū_{v_i}`.
     So `Γ` is finite when the unit groups are finite, and a-T-menable when the `Ū_v` are.
2. **Bounded orbit ⇔ coboundary (minimal case).** If `Γ` acts minimally on `Y`, the hypothesis of 1 holds as
   soon as `{c(γ, z_0) : γ ∈ Γ}` is bounded for one `z_0 ∈ Y`. Conversely, a coboundary has uniformly bounded
   displacement on every orbit.
3. **Consequences.**
   - Let `Γ` be infinite and not residually finite, for example infinite simple or infinite quasisimple.
     On every closed invariant `Y` where it acts faithfully, its degree cocycle is not a continuous
     coboundary. Where it also acts minimally, its level displacement is unbounded along every orbit.
   - Let `Γ` be infinite with property (T), and let the `Ū_v` be a-T-menable. This covers finite, amenable,
     free and cubulated unit groups. Then the degree cocycle of `Γ` is not a continuous coboundary on `Z`.

## Proof

**Three facts about cylinders.** Write `≥` componentwise on `N^k`.
- (N1) *Nesting.* Let `d(x) ≥ d(q)`, `t(x) = t(q)` and `ζ ∈ Z(x) ∩ Z(q)`. By (UFP*), `x = x_1 r` with
  `d(x_1) = d(q)`, and `ζ ∈ Z(x) ⊆ Z(x_1)`. By (P1), `x_1 = qu` with `u` a unit, so `x = q(ur)` and
  `Z(x) ⊆ Z(q)`. So for each `p` the degree-`p` cylinders partition `∂Ω(v)`, larger degrees refine smaller
  ones, and by (P2) and compactness every finite clopen partition is refined by all cylinders of large
  enough degree.
- (N2) *Equal cylinders.* If `Z(x) = Z(y)` and `d(x) = d(y)`, then `y ∈ xℭ*` by (P1).
- (N3) *Normal form.* Every `γ ∈ F(𝒢)` has a depth `P_γ ∈ N^k`. For each `x` with `d(x) ≥ P_γ` there is
  `y` with `s(y) = s(x)` and `γ(xη) = yη` for all `η`, so `c(γ, ·) = d(y) − d(x)` on `Z(x)`.
  - Each arrow has a basic neighbourhood bisection `qrη ↦ prη` on a cylinder. Under finite alignment,
    clopen sets are finite unions of cylinders, which is the description used in
    `finitely-coded-cantor-actions-type-a-proof`, item 1.
  - Finitely many such cylinders `Z(q_i r_i)` cover `Z`. Let `P_γ` dominate their degrees.
  - For `d(x) ≥ P_γ`, (N1) gives `x = q_i r_i r'` for some `i`, and then `y = p_i r_i r'`.

**Item 1.**
- *Normalize `b`.* Adding a constant to `b` keeps the hypothesis, so assume `b ≥ 0`. `b` is locally constant
  with finitely many values `j`. Extend its level sets to a clopen partition `{W_j}` of `Z`, with
  `W_j ∩ Y = {b = j}`.
- *Choose `p`.* Take `p ∈ N^k` so large that:
  - `p` dominates the depths of a finite generating set `S = S^{-1}` of `Γ`;
  - by (N1), every cylinder of degree `≥ p` either lies in a single `W_j` or misses `Z`.
- *The partition.* Let `𝒫_p` be the finite set of cylinders `Z(x)` with `Z(x) ⊆ W_j` and `d(x) = p + j`,
  over all `j`, that meet `Y`. Their traces on `Y` partition `Y`: the piece of `z` is its cylinder of
  degree `p + b(z)`.
- *Generators permute pieces.* Let `s ∈ S` and `Z(x) ∈ 𝒫_p`, with `d(x) = p + j`.
  - Since `d(x) ≥ P_s`, (N3) gives `s(xη) = yη` with `d(y) = d(x) + c(s, z)` for `z ∈ Z(x)`.
  - For `z ∈ Z(x) ∩ Y`, `c(s, z) = b(sz) − j`. So `d(y) = p + b(sz)`, and `s(Z(x) ∩ Y) = Z(y) ∩ Y`
    lies in `{b = b(sz)}`.
  - So `Z(y) ∈ 𝒫_p`, and `s` permutes the traces of the pieces on `Y`. Hence all of `Γ` does, and this
    defines a homomorphism `ρ_p : Γ_Y → Sym(𝒫_p)`.
- *(a) Residual finiteness.* The same holds for every larger `p`. Each piece of `𝒫_p` has degree `≥ p`,
  so by (P2) the pieces shrink to points as `p → ∞`. An element of `∩_p ker ρ_p` fixes every piece
  containing each `z ∈ Y`, hence fixes `z`. So the finite quotients `ρ_p(Γ_Y)` separate `Γ_Y`.
- *(b) The kernel is unit-like when `Y = Z`.* Let `K = ker ρ_p ≤ Γ`, a subgroup of finite index, and let
  `g ∈ K` and `Z(x) ∈ 𝒫_p`.
  - Write `g` as a word in `S`. Applying (N3) letter by letter, each letter maps a piece `Z(x')` onto a piece
    `Z(y')` by `x'η ↦ y'η`. So `g(xη) = x''η` for all `η`, where `Z(x'')` is a piece.
  - `g` fixes the piece `Z(x)`, so `Z(x'') = Z(x)`. Both have degree `p + j` for the common value `j` of
    `b` there.
  - By (N2), `x'' = x u_x(g)` for a unit `u_x(g) ∈ ℭ*(s(x), s(x))`. So `g` acts on `Z(x)` as
    `xη ↦ x·u_x(g)η`, and its image `ū_x(g) ∈ Ū_{s(x)}` is determined by `g`.
  - `g ↦ (ū_x(g))_x` is a homomorphism `K → ∏_{Z(x) ∈ 𝒫_p} Ū_{s(x)}`, because
    `gh(xη) = g(x u_x(h) η) = x u_x(g) u_x(h) η`.
  - It is injective: the pieces cover `Z`, so an element acting trivially through every piece is the
    identity.
- *Corollaries of (b).* Finiteness (for finite units) and a-T-menability pass to subgroups, finite products
  and finite-index overgroups. With finite units this recovers the "if" direction of item 4 of
  `brin-thompson-torsion-has-clopen-fixed-sets`, for every finitely coded groupoid.
- *Why (b) needs `Y = Z`.* For a smaller `Y`, the same map only shows that `ker ρ_p` acts on `Y` through
  the restrictions of unit elements to closed subsets. Those are quotients of subgroups of the `Ū_v`, and
  a-T-menability does not pass to quotients. Residual finiteness, part (a), needs no such step.

**Item 2.** This is the Gottschalk–Hedlund argument, which works for any acting group.
- Let `Γ` act on `Y × Z^k` by `γ(z, w) = (γz, w + c(γ, z))`. This commutes with the translations
  `τ_a(z, w) = (z, w + a)`.
- The orbit of `(z_0, 0)` is bounded, so its closure is compact and contains a minimal closed invariant set
  `M`. The projection of `M` is closed, invariant and nonempty, hence all of `Y`.
- Suppose `(z, w)` and `(z, w + a)` both lie in `M` with `a ≠ 0`. Then `τ_a M` is minimal and meets `M`, so
  `τ_a M = M`, and `M` is invariant under all `τ_{na}`. This contradicts compactness.
- So `M` is the graph of a function `φ : Y → Z^k`. The projection `M → Y` is a continuous bijection of
  compact Hausdorff spaces, hence a homeomorphism, so `φ` is continuous.
- Invariance of `M` gives `c(γ, z) = φ(γz) − φ(z)`.

Conversely, `|b(γz) − b(z)| ≤ 2 max|b|`.

**Item 3.**
- *Non-residually-finite inputs.* If the cocycle were a coboundary on `Y`, part 1(a) would make
  `Γ_Y = Γ` residually finite. Unboundedness then follows from item 2.
  - An infinite simple group is not residually finite.
  - Nor is an infinite quasisimple group `G`. A finite-index normal `N` has image `1` or `G/Z(G)` in the
    infinite simple group `G/Z(G)`. If the image is `1`, then `N ≤ Z(G)` and `G/Z(G)` is finite. If it is
    `G/Z(G)`, then `G/N` is abelian, and perfection gives `N = G`.
- *Kazhdan inputs.* By 1(b), `Γ` would be virtually a subgroup of an a-T-menable group, hence
  a-T-menable. With property (T), that forces `Γ` to be finite.

## Calibrations

- **Units.** For `Γ ≤ ℭ*(v, v)`, take `Z = Y = ∂Ω(v)` and `b = 0`. Part 1(a) recovers
  `finitely-coded-unit-groups-act-residually-finitely` for finitely generated subgroups.
- **Lattices on buildings.** In the orbit-category coding of a cocompact lattice on a tree or Euclidean
  building (`euclidean-building-lattices-lie-in-permutational-bh-class`), `c(γ, ω)` is the Busemann shift
  between the sectors `[O, γω)` and `γ[O, ω)`.
  - A subgroup fixing a vertex `o` has a locally constant coboundary: `b(ω)` is the offset between the
    sectors from `O` and from `o` toward `ω`, which share a subsector.
  - Loxodromic elements have unbounded displacement on the orbit of their attracting chamber.
- **Geometric codings over trees and cube complexes.** A Kazhdan subgroup fixes a vertex of any tree
  (Watatani) or of any finite-dimensional CAT(0) cube complex (Niblo–Reeves). Both imports are context only
  and were not re-read at source.
  - A vertex stabilizer of a locally finite complex acts on each ball, and hence on the boundary, through
    finite groups.
  - So orbit-category codings of tree actions, and the pointed cube codings of
    `cubulated-groups-act-by-bisections-of-a-pointed-cube-category`, carry only residually finite Kazhdan
    subgroups. Here this is immediate from the fixed point; item 1 is the abstract version, which needs no
    geometry.
  - A non-residually-finite Kazhdan input needs one of two things:
    - a coding over a geometry on which Kazhdan groups act without fixed point, such as higher-rank
      Euclidean buildings (Ã₂, C̃₂ and G̃₂ lattices are Kazhdan);
    - a non-geometric coding in which its degree class is nonzero.

## Consequence for the SFT-to-Li bridge (synthesis gate G3g, lane (j))

Take `T = G_V × (Λ ⋉ X)` as in `v-times-minimal-free-sft-alternating-full-groups-are-fp`. The translation
`t_λ` has `V`-degree 0 and preserves each closed invariant set `Y_c = {c} × X`, on which `Λ` acts minimally
and faithfully.
- **What item 1 forces.** Suppose some finitely coded structure `T ≅ 𝒢_ℭ`, or a Kakutani reduction of
  one, makes the degree cocycle of the translations a continuous coboundary on one `Y_c`. By item 2 it is
  enough that one orbit has bounded level displacement. This happens, for instance, when translations act
  level-preservingly, as in a product coding that reads `X` through a hierarchy in which a translation only
  carries between neighbouring supertiles. Then `Λ` is residually finite, by part 1(a).
- **The master route's `Λ`.** Here `Λ = Λ_0 × H`, with `Λ_0` infinite and quasisimple (`St_10(R_L)`), so it
  is not residually finite. So a Li-type proof of P2′ must use a coding in which translations of the
  configuration change level without bound along every orbit. Then `Λ` acts as it would on a boundary, with
  a Busemann-type cocycle.
- **What that means for rigidity.** Quantum rigidity of `X` is not an input to Li's finiteness theorem; the
  missing input is scaling.
- **Calibration of the dichotomy.**
  - For `Λ = Z`, write the two-sided full shift as `A^Z = A^{−N} × A^N`. The shift is the global bisection
    `(p, af) ↦ (pa, f)` of the product of two Cuntz groupoids, of degree `(1, −1)`: one symbol crosses a
    finite interface.
  - Heuristic, not proved: one-ended groups, which is what strongly aperiodic SFTs need (Cohen, context
    only), have no finite interfaces, so this mechanism is unavailable there.
  - Hierarchy codings give translations degree 0. That is allowed for `Z^2`, which is residually finite, and
    excluded for `Λ_0`.

This does not refute P2′. It says which proof shapes are possible:
- a Stein–Farley argument directly on `T` (lane (i)), whose descending links rigidity could control;
- a Li coding built on a boundary-type action of `Λ_0` itself.

## Lesson for general BH

- **Each input splits in two in a finitely coded host.** It has a *scaling part* (its degree class) and a
  *unit part*. A finitely generated input with trivial scaling is, up to finite index, a subgroup of a finite
  product of unit groups.
- **What non-residually-finite inputs need.** Every non-residually-finite input, in particular every
  infinite simple one, must scale without bound along every orbit.
- **Kazhdan inputs.** An infinite Kazhdan input has a nonzero scaling class as soon as the units are
  a-T-menable. Tree and cube geometries admit only residually finite Kazhdan inputs.
- **The design rule.** Hosts built from finite codings must give the hard input a boundary-type action with
  a genuine Busemann cocycle over a higher-rank (Kazhdan-compatible) geometry, and put all remaining
  complexity in residually finite units. Rigidity of an SFT supplies neither.
