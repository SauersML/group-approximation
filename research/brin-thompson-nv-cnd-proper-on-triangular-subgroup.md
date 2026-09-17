---
rg: 2
id: brin-thompson-nv-cnd-proper-on-triangular-subgroup
kind: claim
title: "For n >= 2 the Brin-Thompson group nV carries a cnd function whose restriction to the triangular subgroup T_n is proper"
distinct_from:
  brin-thompson-nv-cnd-proper-modulo-triangular-subgroup: that is the transversal half of the split; this is the fibre half
  cantor-integer-maps-by-v-have-haagerup-property: that is the Haagerup property of the subgroup C(C,Z) ⋊ V ≤ T_2, which this implies; this also asks for the function to extend to all of nV
---

**Statement.** Let `n ≥ 2` and let `T_n ≤ nV` be the triangular subgroup of
`brin-thompson-triangular-subgroup-is-undistorted`. There is a cnd function `ψ_2` on `nV` such
that `{h ∈ T_n : ψ_2(h) ≤ R}` is finite for every `R`.

**Role.** This is the fibre prerequisite of `brin-thompson-nv-a-t-menable-via-triangular-split`.
It is necessary for the Haagerup property of `nV`.

**Consequences if true.**
- `T_n` has the Haagerup property. So do its subgroups `C(C, T_{n−1}) ⋊ V`. For `n = 2` these
  include `C(C,V) ⋊ V` and `C(C,Z) ⋊ V`, which is Brothier's Problem B for `Γ = V` and `Γ = Z`
  (`cantor-integer-maps-by-v-have-haagerup-property`).

**Independence from the transversal half.** Neither half implies the other in any known way.
The transversal half concerns coset geometry and is forced to be non-cubical. This half is a
statement about a subgroup, on which exponent cocycles already grow linearly
(`brin-thompson-triangular-subgroup-is-undistorted`), so the Callard–Salo obstruction does not
apply to `T_n` itself.

## Attempts

- 2026-09-17 (swarm-0917-w4-nv-cocycle). *Induction along the tower.* `T_n` is an extension
  `1 → K_n → T_n → T_{n−1}` with kernel `K_n` the fibre-preserving elements
  `(x', y) ↦ (x', F_{x'}(y))`, which is `C(C^{n−1}, V)`, a locally constant current group. A proper
  cnd function on `T_n` would follow from one on `T_{n−1}` (induction) plus a cnd function on
  `T_n` proper on `K_n`, by the normal-subgroup case of
  `haagerup-splits-as-coset-plus-subgroup-properness`. The base kernel case `n = 2` is Problem B for
  `Γ = V`, so this route does not avoid Problem B, and the extension to all of `nV` is a separate
  issue. The image of `T_n → T_{n−1}` is all of `T_{n−1}`, since `T_{n−1} × V ≤ T_n` acting
  coordinatewise.
