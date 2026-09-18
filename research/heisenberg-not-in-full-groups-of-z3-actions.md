---
rg: 2
id: heisenberg-not-in-full-groups-of-z3-actions
kind: claim
title: "H_3(Z) is not a subgroup of the full group [[Z^3 ↷ X]] of any Z^3-set, so it lies in no W(Z^3) and in no topological full group of a Z^3-subshift"
distinct_from:
  heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs: that kills hosts whose orbit graphs grow quadratically, by a box count; this kills all actions of Z^3, whose orbit graphs Z^3/Λ can grow cubically, by a Pansu blow-down of the displacement map. It uses the quadratic claim only for orbits with a short period vector.
  heisenberg-in-nv-forces-drift-free-central-element: that is a drift condition on H_3 inside nV; this excludes the specific cubic hosts [[Z^3 ↷ X]].
---

**Setting.** `Z^3` acts on a set `X` by `u ↦ T^u`. Its *full group*
`[[Z^3 ↷ X]]` is the group of bijections `g` of `X` for which some finite
`F ⊆ Z^3` has `g x ∈ {T^u x : u ∈ F}` for every `x`. No topology is assumed.
`H = H_3(Z) = ⟨a, b | [a,[a,b]], [b,[a,b]]⟩`, with `c = [a,b]` central of
infinite order.

**Statement.** For every `Z^3`-set `X`, no subgroup of `[[Z^3 ↷ X]]` is
isomorphic to `H`. Precisely, for every homomorphism
`ρ : H → [[Z^3 ↷ X]]`, `ρ(c)` has finite order.

**Special cases.**
- `W(Z^3) = [[Z^3 ↷ Z^3]]`, the bounded-displacement bijections of `Z^3`.
  This answers the question "whether H embeds in W(Z^3)" left open in
  `heisenberg-not-in-wobbling-groups-of-quadratic-growth-graphs` (Sharpness).
- Topological full groups of `Z^3`-subshifts: by compactness, a continuous
  cocycle takes finitely many values.
- The product shift `σ×σ×σ` on `({0,1}^Z)^3`. With Salo's baker's coding its
  full group sits in `6V`, but that remark is not used here.
- Any group containing `H`, e.g. `SL_n(Z)` for `n ≥ 3`, acts faithfully by
  no such full group.

**Consequence for hosts of `H` in `mV`.** Every host whose `H`-orbits move
inside a single `Z^3` coordinate action is dead. Abelian hosts of higher rank
survive: `heisenberg-group-embeds-in-wobbling-group-of-some-zn` puts `H`
inside `W(Z^N)` for some `N`. So any no-answer for `mV` must use more than
orbit growth.

Route: `heisenberg-not-in-full-groups-of-z3-actions-pansu-proof` (unreviewed).
