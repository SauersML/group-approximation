---
rg: 2
id: thompson-t-quad-complete-laminations-carry-no-invariant-mean
kind: claim
title: No Thompson T-set, and no nonsingular T-space with almost invariant Koopman vectors, maps equivariantly to the quad-complete laminations with endpoints in a countable T-invariant set; so no subgroup of a stabilizer of the dyadic Farey tessellation is co-amenable in T
distinct_from:
  thompson-t-orbits-carry-no-invariant-means: that bounds finite subsets of the circle under T; this excludes invariant means on spaces of chord systems (laminations), which do not map to S^1 and are not orbits of points
  lifted-thompson-t-convex-line-walls-are-trivial: that excludes T-invariant Radon measures on pairs of circle points, where a single pair is the object; here a whole non-crossing chord system is the object and the mean is finitely additive, and the contradiction comes from quad-diagonal exclusivity, not from contracting a rectangle
  thompson-t-co-amenable-subgroup-kills-real-euler-class: that asks for a co-amenable H in T with vanishing real Euler class; this proves that no H inside a stabilizer of a quad-complete lamination is co-amenable, and says nothing about the Euler class
  thompson-t-euler-class-splits-over-almost-invariant-space: that asks for a measurable Euler splitting over some almost invariant T-space; this excludes every candidate space that maps measurably to quad-complete laminations, whatever the cocycle
artifacts: []
---

**ESTABLISHED.** The proof is `thompson-t-quad-complete-laminations-diagonal-proof`.

## Setting

- `T` acts on `S^1 = R/Z` by dyadic piecewise-linear homeomorphisms.
- `D ⊂ S^1` is a countable `T`-invariant set, for example the dyadic rationals `Z[1/2]/Z`.
- A **chord** is an unordered pair `{p, q}` of distinct points of `S^1`. Two chords **cross**
  if their endpoints are distinct and interleave in the cyclic order.
- A **quad** is a cyclically ordered 4-tuple `a < b < c < d` of points of `S^1 \ D`. Its open
  arcs are `I_1 = (a,b)`, `I_2 = (b,c)`, `I_3 = (c,d)`, `I_4 = (d,a)`.
- For disjoint open arcs `A, B` and a chord set `τ`, put `f_{A,B}(τ) = 1` if some chord of `τ`
  has one endpoint in `A` and one in `B`, and `0` otherwise.
- `Tri_D` is the set of chord sets `τ` such that
  - all endpoints of chords of `τ` lie in `D`;
  - no two chords of `τ` cross;
  - `τ` is **quad-complete**: for every quad, `f_{I_1,I_3}(τ) = 1` or `f_{I_2,I_4}(τ) = 1`.

`T` acts on `Tri_D` by `g·τ = {{gp, gq} : {p,q} ∈ τ}`.

## Statement

1. **Discrete.** Let `X` be a `T`-set with a `T`-equivariant map `π : X → Tri_D`. Then
   `ℓ^∞(X)` has no `T`-invariant mean.
2. **Measurable.** Let `(X, μ)` be a standard σ-finite space with a nonsingular `T`-action, and
   let `π : X → Tri_D` be equivariant μ-a.e. and measurable, meaning each `x ↦ f_{A,B}(πx)` is
   measurable. Then the Koopman representation of `T` on `L^2(X, μ)` has no almost invariant
   unit vectors.
3. **The dyadic Farey tessellation is in `Tri_D`.** Let `D` be the dyadic rationals and let
   `τ_0 = {{k/2^n, (k+1)/2^n} : n ≥ 1, k ∈ Z}`. Then `g·τ_0 ∈ Tri_D` for all `g ∈ T`.
4. **Subgroup consequence.** If `H ≤ T` fixes some `τ ∈ Tri_D`, then `H` is not co-amenable in
   `T`. This applies in particular to every `H ≤ g Stab_T(τ_0) g^{-1}`. By the standard
   Minkowski question-mark conjugacy (`?` sends Farey neighbours to dyadic neighbours, which
   identifies `T` with Thompson's piecewise-`PSL_2(Z)` group), this includes every conjugate in
   `T` of the copy of `PSL_2(Z)` in `T` and all of its subgroups.

## Named obstruction

The invariant is **sharp quad-diagonal exclusivity**, which comes in two parts:
- `f_{A,B}` is `{0,1}`-valued and monotone in `A` and in `B`;
- for every quad, exactly one of `f_{I_1,I_3}` and `f_{I_2,I_4}` equals `1`.

Take any invariant mean `m`, and set `ν(A,B) = m(f_{A,B} ∘ π)`.
- Transitivity of `T` on cyclically ordered dyadic 4-tuples makes `ν` constant on pairs of arcs
  with disjoint closures.
- Monotonicity then gives `m|f_{A,B} − f_{A',B'}| = 0` for nested pairs.
- A chain of five nested moves joins `(I_1, I_3)` to `(I_2, I_4)`. It forces
  `m|f_{I_1,I_3} − f_{I_2,I_4}| = 0`.
- Pointwise, however, `|f_{I_1,I_3} − f_{I_2,I_4}| = 1`.

Every candidate witness dies at this monotone-sandwich chain.

## Consequences for the Euler-splitting routes

- **Discrete route** (`thompson-t-co-amenable-subgroup-kills-real-euler-class`). This gives a
  new forced shape: a co-amenable `H` fixes no quad-complete lamination with endpoints in a
  countable `T`-invariant set.
  - This contains the forced shape (D3) that swarm-0917-w10 obtained for conjugates of
    `PSL_2(Z)` through almost malnormality and a Kesten gap.
  - It adds the stabilizers of every other quad-complete lamination `τ ∈ Tri_D`. Examples are
    the locally finite ideal triangulations with vertices in `D` that are not in the `T`-orbit
    of `τ_0`, and triangulations with vertices in other countable orbits `D`.
  - The proof needs no malnormality and no spectral estimate.
- **Measurable route** (`thompson-t-euler-class-splits-over-almost-invariant-space`, (MT)). A
  witness space `X` admits no measurable equivariant map to `Tri_D`, whatever the cocycle `β`.
  This kills, for example:
  - the spaces of random ideal triangulations with dyadic vertices;
  - the Farey-type tessellation spaces `T/Stab(τ)` with any quasi-invariant measure;
  - every space fibred over them.

## What does not die

- **Fuzzy deciders.** `[0,1]`-valued deciders with `f_{13} + f_{24} = 1` pass the test, for
  example the constant `1/2`. The chain uses `|f − f'| = f' − f`, which needs `{0,1}` values.
- **Laminations that are not quad-complete.** Examples are a single chord, or `τ_0` with the
  chord `{0, 1/2}` removed. The latter fails at a quad whose four arcs contain `0`, `1/4`,
  `1/2` and `3/4` respectively, with `I_1, I_3` inside `(−1/8, 1/8)` and `(3/8, 5/8)`. For
  such spaces the pointwise identity `f_{13} + f_{24} = 1` is lost, and the argument gives
  nothing.
- **Endpoint sets that are not countable and invariant.** Countable endpoint sets that vary with
  the point of `X` are handled in the measurable case by Fubini (see the Remark in the proof).
  In the discrete case they are not handled.
