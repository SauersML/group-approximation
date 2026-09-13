---
rg: 2
id: mixing-nonsofic-action-from-sl3z-lattice-space-action
kind: route
title: A nonsofic lattice-space action is a free mixing nonsofic action of the sofic group SL3(Z)
target: mixing-free-nonsofic-action-of-sofic-group
requires:
  - sl3z-lattice-space-action-is-not-sofic
  - howe-moore-property-for-simple-lie-and-p-adic-groups
---

Conditional route; it fires when `sl3z-lattice-space-action-is-not-sofic` is established.

1. **Free.** The fixed set of `γ != 1` in `SL_3(R)/SL_3(Z)` is a countable union of translates of proper
   centralizers, a Haar null set (freeness paragraph of
   `induced-actions-sofic-iff-homogeneous-action-sofic-proof`). This is elementary and needs no claim.
2. **Mixing.** `SL_3(R)` acts transitively, hence ergodically, on `SL_3(R)/SL_3(Z)`. It has the
   Howe--Moore property (`howe-moore-property-for-simple-lie-and-p-adic-groups`), so the Koopman
   coefficients on `L²_0` are `C_0` on `SL_3(R)`. The discrete subgroup `SL_3(Z)` meets every compact set
   finitely, so the coefficients tend to `0` along `SL_3(Z)`.
3. **Sofic group.** `SL_3(Z)` is residually finite (congruence quotients), hence sofic.
4. **Not sofic** by hypothesis.
