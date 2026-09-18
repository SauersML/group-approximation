---
rg: 2
id: lifted-thompson-t-convex-line-walls-are-trivial
kind: claim
title: Every T-bar-invariant measured wall structure on the line with order-convex walls gives a bounded cnd function, because Thompson's T preserves no nonzero Radon measure on pairs of distinct circle points
distinct_from:
  thompson-t-is-not-amenable: that excludes a T-invariant probability measure on the circle S^1; this also excludes T-invariant Radon measures on the non-compact pair space S^1 x S^1 minus the diagonal (invariant "geodesic currents"), where infinite total mass is allowed, and applies this to walls of the lifted line
  thompson-t-orbits-carry-no-invariant-means: that is a uniform isoperimetric bound for finite subsets of the circle under T; this is a statement about invariant Radon measures on pairs and about wall structures of T-bar, not about finite sets
  lifted-thompson-t-is-a-t-menable: that is the open Haagerup question for T-bar; this kills one class of approaches to it and does not decide it
artifacts: []
---

**ESTABLISHED.** Let `T` be Thompson's group of dyadic piecewise-linear homeomorphisms of
`S^1 = R/Z`, and let `T̄` be its lift to `R`, with central element `z(x) = x + 1`. Put
`U = (S^1 × S^1) \ Δ`.

1. **No invariant geodesic currents.** Every `T`-invariant Radon measure on `U` is zero.
   Every `T`-invariant Radon (so finite) measure on `S^1` is zero.
2. **Convex walls on the line are trivial.** Consider the walls `{h, R \ h}` of `R`, where `h`
   is order-convex. Let `μ` be a `T̄`-invariant Borel measure on this space of walls, and
   suppose the walls separating any two points `p ≠ q` of `R` have finite measure `d(p,q)`.
   Then:
   - `μ` vanishes on every wall whose convex side has two distinct endpoints, and on every cut
     (a wall whose sides are half-lines);
   - `d(p,q) = μ{p} + μ{q}`, the mass of the singleton walls at `p` and at `q`;
   - the cnd function `ψ_p(g) = d(p, g p)` equals `2μ{p}` or `0`. It is **bounded on all of
     `T̄`**, and in particular it is bounded on the centre `⟨z⟩`.
3. **Pullbacks.** The same holds for walls on any `T̄`-set `X` pulled back along a
   `T̄`-equivariant map `X → R`. More generally, it holds whenever the walls of `X` are indexed
   `T̄`-equivariantly by intervals or cuts of `R`, through a measure on the index space that is
   finite on compact sets. That measure vanishes off the singletons.

Proof: `lifted-thompson-t-convex-line-walls-contraction-proof`.

## Role

By `lifted-thompson-t-is-a-t-menable` (Equivalent form), `T̄` is Haagerup iff some cnd
function is proper on `⟨z⟩`. This claim shows that no such function comes from the order
structure of the line that `T̄` acts on. That order structure is the only place where the
central direction is visible geometrically: `z` translates `R`, and it acts trivially on the
Stein–Farley complex of `T`.

**Which class dies, and where.** The class is the "lifted Liouville" template: build walls
for a lifted circle group out of arcs, or intervals of `R`, weighted by an invariant measure on
pairs of endpoints.
- The template is modelled on lattices `Γ ≤ PSL_2(R)`. There the Liouville current
  `dx dy / sin²(π(x − y))` on `U` is a nonzero `PSL_2(R)`-invariant Radon measure.
- For `T̄`, **every member of the class dies at one step: the index measure on pairs, taken in
  each winding class, is a `T`-invariant Radon measure on `U` or on `S^1`, and so it is zero
  by (1).**
- The invariant is the cone of `T`-invariant Radon measures on `U`. It is `{0}` for `T`, and
  nonzero for Fuchsian groups.

So a proof that `T̄` is Haagerup has to use walls that are not order-convex on the lifted line,
and not indexed by intervals of it. Such walls might be combinatorial ones, like Farley's, but
then they must see the winding, which the Stein–Farley walls do not.

A refutation through `lifted-thompson-t-center-has-relative-t` cannot be obtained just by
excluding this class. The claim says nothing about non-convex walls.
