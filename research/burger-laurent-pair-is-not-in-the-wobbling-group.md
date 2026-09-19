---
rg: 2
id: burger-laurent-pair-is-not-in-the-wobbling-group
kind: claim
title: "EL_2(F_p[t,t^-1]) ⋉ F_p[t,t^-1]^2 does not embed in the wobbling group of Z, hence not in the full-shift topological full group"
distinct_from:
  full-shift-full-group-has-infinite-normal-relative-t-subgroup: that asks for any infinite normal relative-(T) subgroup in [[X]]; this rules out its one named candidate
  burger-laurent-pair-wobbling-point-kernels-are-congruence: that constrains every embedding unconditionally; this is the non-existence, which also needs property (tau)
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that concerns Kazhdan groups; this group does not have (T), only relative (T) over its base
---

**OPEN.** The only open prerequisite is the Selberg property
`laurent-sl2-positive-characteristic-has-selberg-property`.

**Statement.** For every prime `p`, `Γ_p = EL_2(F_p[t, t^{-1}]) ⋉ F_p[t, t^{-1}]²` is not isomorphic
to a subgroup of `W(Z)`. Since `[[X]] ≤ W(Z)` for the full shift `X`, `Γ_p` does not embed in `[[X]]`.

**Role.** This kills the named candidate of
`full-shift-full-group-has-infinite-normal-relative-t-subgroup`. The kill is independent of
the realization chosen: lamplighter, Salo-type, or any other.

Route: `burger-laurent-pair-not-in-wobbling-group-from-selberg-proof`.
