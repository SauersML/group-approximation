---
rg: 2
id: heisenberg-group-embeds-in-wobbling-group-of-some-zn
kind: claim
title: "H_3(Z) embeds in the wobbling group W(Z^N) = [[Z^N ↷ Z^N]] for some N, so orbit growth alone cannot exclude it from abelian full groups"
distinct_from:
  heisenberg-not-in-full-groups-of-z3-actions: that excludes H_3 from full groups of Z^3-actions; this puts H_3 inside the full group of the translation action of Z^N for some larger N.
  heisenberg-group-embeds-in-some-brin-thompson-group: that asks for H_3 inside mV; this is an abelian-host embedding that does not by itself give any element of mV.
---

**Statement.** There is `N` and an injective homomorphism
`H_3(Z) → W(Z^N)`, where `W(Z^N)` is the group of bijections `g` of `Z^N`
with `sup_x |g x − x| < ∞`.

**Meaning for the `mV` question.**
- `heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs` and
  `heisenberg-not-in-full-groups-of-z3-actions` kill abelian hosts of rank
  `≤ 3` by growth and blow-down.
- This claim shows the method cannot go further by counting alone. Any proof
  that `H_3(Z) ⊄ mV` must use structure that `W(Z^N)` lacks: prefix locality,
  or the product structure of shift coordinates.
- Product shifts of dimension `N ≥ 4` inside `mV` (baker's coding) and
  reversible-Turing-machine hosts remain open.

Route: `heisenberg-group-embeds-in-wobbling-group-of-some-zn-proof`
(unreviewed).
