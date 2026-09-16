---
rg: 2
id: brin-thompson-2v-not-a-t-menable-via-cantor-integer-maps
kind: route
title: "Reduce the negative side to a negative answer to Brothier's Problem B for Γ = Z"
target: brin-thompson-2v-is-not-a-t-menable
requires:
  - cantor-integer-maps-by-v-are-not-a-t-menable
  - cantor-maps-by-v-embed-in-next-brin-thompson-group
---

## Why sufficient

By `cantor-maps-by-v-embed-in-next-brin-thompson-group` with `n = 1` and
`Γ = ⟨s⟩ ≅ Z ≤ V`, the group `G = C(C,Z) ⋊ V` is a subgroup of `2V`. The Haagerup
property passes to subgroups, since restricting a proper cnd function to a subgroup
keeps it proper and cnd. So if `G` is not a-T-menable
(`cantor-integer-maps-by-v-are-not-a-t-menable`), neither is `2V`.

A concrete sufficient input is relative property (T) of `(G, C(C,Z))`, or of any
infinite subset of `C(C,Z)`. The artifact §3(f) translates this into
non-existence of `V`-almost-invariant probability measures on the dual concentrating
at `0`. This replaces the search for Kazhdan subgroups or affine `Z^2 ⋊ SL_2`
copies inside `2V`, recorded in the target's Attempts, with a question about one
explicit abelian-by-`V` subgroup.
