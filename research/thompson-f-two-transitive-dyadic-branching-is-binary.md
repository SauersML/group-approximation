---
rg: 2
id: thompson-f-two-transitive-dyadic-branching-is-binary
kind: claim
title: In a 2-transitive action of Thompson's group F, the orbit of the left rigid stabilizer of a dyadic point splits into at most two orbits of its germ-trivial part
distinct_from:
  thompson-f-two-transitive-hull-endpoints-are-rational: that claim shows the hull endpoints of pairs are rational and swaps are nontrivial near them; this claim shows the branching of the abstract set at a dyadic point is binary, and turns it into a slope-parity condition on the point stabilizer
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim compares orbits of the left and right halves at one point; this claim compares, on the left side only, the orbits of the half with those of its germ-trivial part
---

Let `F` act on `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. Fix `ω ∈ Ω`, `H = F_ω`, and a dyadic `p ∈ (0,1)`. Let `F_p^-` be the
elements supported in `[0,p]`, `M_p = ∪_{y<p} F_y^-` its subgroup of elements
that are the identity near `p`, and `λ_p : F_p^- → Z` the base-2 logarithm of
the left slope at `p`. For `ω' ≠ ω` let `η(ω,ω')` be the hull endpoint of
`thompson-f-two-transitive-hull-endpoints-are-rational`. Then:

1. `F_p^- ω` is the union of at most two `M_p`-orbits.
2. If it is one orbit, then `λ_p(H ∩ F_p^-) = Z`.
3. If it is two orbits, then `λ_p(H ∩ F_p^-) = 2Z`, the elements of odd slope
   exchange the two orbits, and
   `F_p^- ω \ M_p ω = {ω' : η(ω,ω') = p}`.
4. (Dichotomy.) Two orbits occur for some `(ω,p)` if and only if the orbit
   `Θ^-` of hull endpoints is the dyadic orbit and every pair attains its
   endpoint, i.e. `ω' ∈ F^-_{η(ω,ω')} ω` for all `ω ≠ ω'`. In that case, for
   every `ω`, the set of dyadic `p` with two orbits is exactly
   `P_ω = {η(ω,ω') : ω' ≠ ω}`, a single `F_ω`-orbit.
5. (Parity.) In the two-orbit case, if `h ∈ H` fixes `p ∈ P_ω`, then the left
   slope of `h` at `p` is an even power of `2`.

The mirror statements hold for `F_p^+`, `∪_{x>p} F_x^+`, right slopes and `ξ`.

So a point stabilizer of a 2-transitive action is of one of two kinds. In the
first kind, `H ∩ F_p^-` realizes every left slope at every dyadic `p`, and no
pair attains a dyadic hull endpoint. In the second kind, a Jones-type parity
condition holds on the `H`-orbit `P_ω` (dense, by item 2 of
`thompson-f-two-transitive-stabilizers-minimal-not-confined`). Jones' subgroup `\vec F` shows the
second kind of slope rule: an element fixing a dyadic `t` has
`J(g) ∋ t` iff `log₂ g'_−(t)` is odd
(`jones-subgroup-cosets-form-a-parity-lamplighter`). `\vec F` is not itself a
candidate, since it is not maximal (point stabilizers of 2-transitive actions
are maximal by `thompson-f-two-transitive-stabilizers-minimal-not-confined`).
Indeed, by item 2 of the lamplighter claim, `g ↦ |J(g)| mod 2` is a
homomorphism `F → Z/2` whose kernel contains `\vec F`, and by its item 4 some
`g` has `J(g) = {1/2}` and some `g` has `J(g) = {1/2, 3/4}`. So
`\vec F < ker < F`, both strictly.

Scope: refereed by a swarm agent on 2026-09-16 (every step of the route
checked); no independent human review. No novelty is claimed; a web search on
2026-09-16 found no published statement of this dichotomy.

**Proof:** `thompson-f-two-transitive-dyadic-branching-binary-proof`.
