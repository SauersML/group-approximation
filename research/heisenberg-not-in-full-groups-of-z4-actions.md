---
rg: 2
id: heisenberg-not-in-full-groups-of-z4-actions
kind: claim
title: "H_3(Z) is not a subgroup of the full group [[Z^4 ↷ X]] of any Z^4-set, so it lies in no W(Z^4) and in no topological full group of a Z^4-subshift"
distinct_from:
  heisenberg-not-in-full-groups-of-z3-actions: that kills rank-3 actions using only a stabilizer bound, which loses one power of the radius. This kills rank 4, the first rank where that loss is fatal. It uses exact local freeness to keep the full quartic lower count.
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that is a box count for quadratic orbit growth; this allows quartic orbit growth Z^4/Λ.
  heisenberg-group-embeds-in-wobbling-group-of-some-zn: that is the positive statement H ≤ W(Z^N) for some large N; this shows N ≥ 5 is needed.
---

**Setting.** `Z^4` acts on a set `X` by `u ↦ T^u`. Its *full group*
`[[Z^4 ↷ X]]` is the group of bijections `g` of `X` for which some finite
`F ⊆ Z^4` has `g x ∈ {T^u x : u ∈ F}` for every `x`. No topology is assumed.
`H = H_3(Z) = ⟨a, b | [a,[a,b]], [b,[a,b]]⟩`, with `c = [a,b]`.

**Statement.** For every `Z^4`-set `X`, no subgroup of `[[Z^4 ↷ X]]` is
isomorphic to `H`. Precisely, every homomorphism `ρ : H → [[Z^4 ↷ X]]` has
`ρ(c)` of finite order.

**Special cases.**
- `W(Z^4) = [[Z^4 ↷ Z^4]]`. This settles "the first open case is `W(Z^4)`",
  recorded in the Attempts of `heisenberg-group-embeds-in-some-brin-thompson-group`
  (2026-09-18) and in §6 of `heisenberg-not-in-full-groups-of-z3-actions-pansu-proof`.
- `W(Z^d)` and `[[Z^d ↷ X]]` for `d ≤ 4`. A `Z^d`-action is a `Z^4`-action
  in which the last coordinates act trivially.
- Topological full groups of `Z^4`-subshifts, since continuous cocycles take
  finitely many values.
- The full group of the product shift `σ^{×4}` on `({0,1}^Z)^4`. With Salo's
  baker's coding it sits in `8V`, so that host of `H` in `8V` is dead.

**Consequence.** Among hosts whose `H`-orbits stay inside the orbits of one
abelian action, the smallest possible rank is now `5`. The live abelian
questions are `W(Z^N)` and product shifts for `5 ≤ N`, up to the unknown
rank given by `heisenberg-group-embeds-in-wobbling-group-of-some-zn`.

**Why rank 4 is special.** The same blow-down fails for `N ≥ 5`, since an
`ε`-thick neighbourhood of a plane in `R^N` holds `~ε^{N−2}ρ^N` lattice points
at scale `ρ`, which is more than `ρ^4`. A no-answer for `W(Z^5)` needs more
than injectivity plus a first-order Pansu flattening.

Route: `heisenberg-not-in-full-groups-of-z4-actions-proof` (unreviewed).
