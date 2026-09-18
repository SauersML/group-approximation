---
rg: 2
id: twisted-brin-thompson-groups-embed-along-equivariant-inclusions
kind: claim
title: A twisted Brin-Thompson group SV_G embeds in S'V_G' whenever G <= G' acts faithfully on a G-invariant subset S of S'
distinct_from:
  twisted-brin-thompson-finite-presentation-criterion: that decides when one SV_G is finitely presented; this compares two twisted Brin-Thompson groups and says nothing about finite presentation.
  one-fp-simple-group-contains-every-brin-thompson-subgroup: that exhibits one finitely presented simple SV_G containing every nV; this is the functoriality that lets such a host absorb other twisted groups.
---

**ESTABLISHED** (lane proof, not reviewed; elementary). No priority claimed; this is
the kind of functoriality Belk–Zaremsky's definition invites, and I did not check
whether their paper states it.

**Statement.** Let `G'` act on a set `S'`, let `G ≤ G'`, and let `S ⊆ S'` be
`G`-invariant with `G` acting **faithfully** on `S`. Then the twisted Brin–Thompson
group `SV_G` (for the restricted action `G ↷ S`) is isomorphic to a subgroup of
`S'V_{G'}`.

**Corollary.** Let `U = DV_F` be the finitely presented simple group of
`one-fp-simple-group-contains-every-brin-thompson-subgroup` (Thompson's `F` on the
dyadic rationals `D` of `(0,1)`). Then `U` contains `SV_G` for every subgroup `G ≤ F`
and every `G`-invariant `S ⊆ D` on which `G` acts faithfully. For instance:
- `ZV_Z`, with `Z` acting on itself by translation: take `G = ⟨a⟩` for a one-bump
  element `a ∈ F` and `S` the `a`-orbit of a dyadic point in its support. `ZV_Z` is
  simple (faithful action) and not finitely presented (Zaremsky's criterion fails:
  the pairs `{k, k+d}` give infinitely many orbits of 2-element subsets), and it now
  sits in a finitely presented simple group.
- `DV_{F'}` for the commutator subgroup `F'`, and `DV_{F_I}` for the subgroup `F_I`
  of `F` supported in a dyadic interval `I` acting on `D ∩ I`.

## Proof

Write `C = {0,1}^N`. In Belk–Zaremsky's description, an element `f ∈ SV_G` is a
homeomorphism of `C^S` for which there are finitely many clopen pieces `P_1, …, P_k`
partitioning `C^S`, each a product of cylinders on finitely many coordinates, and on
each `P_i` the map is a canonical prefix replacement (on finitely many coordinates)
composed with the coordinate permutation `x ↦ x∘g_i^{-1}` for some `g_i ∈ G`. The
set of all such homeomorphisms is a group containing the generators of `SV_G` (the
untwisted `SV` and `G`). Because `G` acts faithfully on `S`, the permutation of
coordinates on `P_i` determines `g_i`; refining a piece does not change its label,
and composing two such maps multiplies labels on a common refinement.

Put `C^{S'} = C^S × C^{S'∖S}`. Define `ι(f)` on `P_i × C^{S'∖S}` as the same prefix
replacement on the `S`-coordinates, composed with the permutation of **all**
coordinates of `S'` by `g_i`. Since `S` is `g_i`-invariant, `g_i` permutes `S'∖S`
too, so `ι(f)` is a homeomorphism of `C^{S'}` of the same piecewise shape, with
labels in `G ≤ G'`.
- `ι` is a homomorphism: on a common refinement, prefix replacements compose and
  labels multiply in `G`, and the permutation of `S'∖S` composes the same way.
- `ι` is injective: restricting `ι(f)` to the `S`-coordinates recovers `f`.
- `ι` sends the untwisted `SV` into the untwisted `S'V`, and `g ∈ G` to `g ∈ G'`. So
  `ι(SV_G) ≤ S'V_{G'}`.

For the corollary, `F ≤ F` acts on `D`, and restrict to `G ≤ F`. A one-bump
`a ∈ F` has infinite order and moves every dyadic point `p` in the interior of its
support along an infinite orbit, on which `⟨a⟩ ≅ Z` acts by translation, faithfully.
`ZV_Z` is simple because the action is faithful (Belk–Zaremsky, via
`twisted-brin-thompson-finite-presentation-criterion`). ∎
