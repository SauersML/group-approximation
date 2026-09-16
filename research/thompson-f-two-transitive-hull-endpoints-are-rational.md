---
rg: 2
id: thompson-f-two-transitive-hull-endpoints-are-rational
kind: claim
title: In a 2-transitive action of Thompson's group F, the hull endpoints of every pair are rational, and no swap is the identity near them
distinct_from:
  thompson-f-two-transitive-actions-satisfy-grid-condition: that claim gives the grid and splitting at each point x; this claim uses the grid to show the invariant hull endpoints of a pair of points of the abstract set are rational, with every swap nontrivial near them
  thompson-f-two-transitive-rigid-stabilizers-fix-no-point: that claim says no rigid-stabilizer group fixes a point of the abstract set; this claim constrains the invariant points of (0,1) attached to a pair of points of the abstract set
---

Let `F` act on a set `Ω`, `|Ω| ≥ 3`, transitively on ordered pairs of distinct
points. For `x ∈ (0,1)` let `F_x^-` and `F_x^+` be the elements of `F`
supported in `[0,x]` and in `[x,1]`. For `ω ≠ ω'` in `Ω` put

- `I^-(ω,ω') = {x ∈ (0,1) : ω' ∈ F_x^- ω}`, an up-set of `(0,1)`;
- `I^+(ω,ω') = {x ∈ (0,1) : ω' ∈ F_x^+ ω}`, a down-set of `(0,1)`;
- `η(ω,ω') = inf I^-(ω,ω')` and `ξ(ω,ω') = sup I^+(ω,ω')`, the hull endpoints.

Then:

1. `I^-` and `I^+` are nonempty and proper, so `0 < η(ω,ω') < 1` and
   `0 < ξ(ω,ω') < 1`. Moreover `I^- ∩ I^+ = ∅`, so `ξ(ω,ω') ≤ η(ω,ω')`.
   Both are symmetric in `ω,ω'`, and
   `η(gω,gω') = g(η(ω,ω'))`, `ξ(gω,gω') = g(ξ(ω,ω'))` for `g ∈ F`.
2. If `s ∈ F` swaps `ω` and `ω'`, then `s` fixes `η(ω,ω')` and `ξ(ω,ω')`,
   and `s` is the identity on no open interval containing `η(ω,ω')`, and on no
   open interval containing `ξ(ω,ω')`.
3. `η(ω,ω')` and `ξ(ω,ω')` are rational. If `η(ω,ω')` is not dyadic, every
   swap `s` is affine near `η` with slope `2^k`, `k ≠ 0`. The same holds for `ξ`.
4. There is a single `F`-orbit `Θ^-` of rational points of `(0,1)` containing
   `η(ω,ω')` for all `ω ≠ ω'`, and a single `F`-orbit `Θ^+` containing every
   `ξ(ω,ω')`.
5. Let `p = η(ω,ω')` (or `ξ(ω,ω')`), let `Γ_p` be the group of germs at `p` of
   elements of `F` fixing `p` (`Γ_p ≅ Z^2` for dyadic `p`, via left and right
   slopes; `Γ_p ≅ Z` for non-dyadic rational `p`), and let `ρ` be the germ map
   on the setwise stabilizer of `{ω,ω'}`. Then `L = ρ(F_ω ∩ F_{ω'})` is a
   subgroup of `Γ_p`, and for every swap `s`: `ρ(s) ∉ L` and `ρ(s)^2 ∈ L`. So
   `Γ_p/L` has an element of order 2, and two-point stabilizers have
   nontrivial germs at `p`.

So any 2-transitive action gives a rational "last disagreement point" to each
pair. A candidate stabilizer `H = F_ω` is ruled out as soon as some `g ∉ H`
has an irrational value of `η(ω,gω) = g(ζ(g))`, where
`ζ(g) = inf{z ∈ (0,1) : g agrees on [z,1] with some element of H}`, or as soon
as two pairs have hull endpoints in different `F`-orbits.

Scope: refereed by a swarm agent on 2026-09-16 (every step of the route
checked); no independent human review. No novelty is claimed. These are
elementary consequences of the grid condition of Le Boudec–Matte Bon
(arXiv:1906.05744v3, Prop. 5.1), and the hull `[ξ,η]` with swaps fixing both
endpoints was already sketched (with the letters exchanged) in the Attempts of
`thompson-f-has-no-faithful-2-transitive-action`. Added relative to the repo:
rationality, the non-identity of swaps near the endpoints, the single orbits
`Θ^±` and the germ statement. A web search on 2026-09-16 found no published
statement of these items and no resolution of Problem 2.20.

**Proof:** `thompson-f-two-transitive-hull-endpoints-rational-proof`.
