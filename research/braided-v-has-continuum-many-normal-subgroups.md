---
rg: 2
id: braided-v-has-continuum-many-normal-subgroups
kind: claim
title: bV has continuum many normal subgroups inside [P_br, P_br] and an infinite strictly ascending chain of normal subgroups
artifacts:
  - research/artifacts/braided-v-continuum-normal-subgroups-2026-09-16.md
distinct_from:
  every-quotient-of-braided-v-is-finitely-presented: that claim asserts max-n for bV; this claim exhibits continuum many normal subgroups and a strictly ascending chain, which refutes it
  braided-v-max-n-above-lower-central-terms: that claim is ACC among normal subgroups containing a fixed gamma_c(P_br); the subgroups here contain no gamma_c(P_br), so they escape every bounded depth
---

For the braided Thompson group `bV = V_br`, with pure braided kernel `P_br = ker(V_br -> V)`:

- `V_br` has exactly `2^aleph_0` normal subgroups, and continuum many of them lie inside `[P_br, P_br]`.
- There is an infinite strictly ascending chain `N_1 < N_2 < …` of normal subgroups of `V_br`, all inside
  `[P_br, P_br]`.

The union of that chain is therefore a normal subgroup that is not the normal closure of finitely many elements.
So `V_br` does not satisfy max-n.

The same subgroups are normal in `F_br`, so the same statements hold for `F_br` (artifact §6).
