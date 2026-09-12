---
rg: 2
id: thompson-v-has-no-rigid-compression-defect
kind: claim
title: Every rigid pair inside Thompson's V is finite and has trivial defect in every ambient group
invalidates:
  - thompson-v-not-sofic-via-rigid-defect
  - thompson-v-not-hyperlinear-via-rigid-defect
distinct_from:
  a-t-menable-groups-have-no-rigid-compression-defect: that is the general statement for a-T-menable groups; this is its instance for V and its subgroups, together with the explicit non-Kazhdan cylinder defects V does carry.
  thompson-v-carries-nontrivial-rigid-defect: that is the refuted premise a rigid-defect proof of nonsoficity of V would need; this is the established obstruction refuting it.
  kun-thom-wreath-carries-rigid-defect: that exhibits a nontrivial defect over an infinite Kazhdan pair in the Kun--Thom wreath; this shows no such pair exists inside V.
---

**ESTABLISHED.** Let `H` be any group containing Thompson's `V`, and let
`Gamma <= G <= V` be Kazhdan with `Gamma` infranormal in `G`. Then `G` is finite,
`Gamma` is normal in `G`, and `D_H(G, Gamma) = 1`.

So neither `sofic-groups-kill-rigid-compression-defects` nor
`hyperlinear-groups-kill-rigid-compression-defects` can be fed a witness taken
from inside `V`. Both routes that would do so are dead:
`thompson-v-not-sofic-via-rigid-defect` and
`thompson-v-not-hyperlinear-via-rigid-defect`.

## The defect `V` does carry, and why it does not count

`V` is full of infranormal subgroups with nontrivial compression defects. Only
property (T) is missing. Let `V_C` be the rigid stabilizer of a proper cylinder `C`
(the elements supported in `C`), so `V_C` is isomorphic to `V`. Let `t` be the prefix
replacement `{0,10,11} -> {00,01,1}`. Then `t V_(0*) t^-1 = V_(00*)` is properly
contained in `V_(0*)`. The subgroup `V_(1*)` centralizes `V_(0*)`. For `z in V_(1*)`
the conjugate `t z t^-1` lies in `V_(01* u 1*)`, which meets `0*` in `01*`, so
`[t z t^-1, gamma] != 1` for suitable `gamma in V_(0*)`. This is the cylinder shape of
the Kun--Thom defect. It gives nothing here because `V_(0*)` is a-T-menable.

Derivation: `thompson-v-has-no-rigid-compression-defect-proof`.
