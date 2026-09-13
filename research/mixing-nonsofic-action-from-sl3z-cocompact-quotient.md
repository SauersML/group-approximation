---
rg: 2
id: mixing-nonsofic-action-from-sl3z-cocompact-quotient
kind: route
title: A nonsofic action of SL3(Z) on a cocompact lattice quotient is a free mixing nonsofic action of a sofic group
target: mixing-free-nonsofic-action-of-sofic-group
requires:
  - sl3z-on-cocompact-lattice-quotient-is-not-sofic
  - howe-moore-property-for-simple-lie-and-p-adic-groups
---

Conditional route. It fires when `sl3z-on-cocompact-lattice-quotient-is-not-sofic` is established.

1. **Free.** For `γ != 1`, the fixed set in `SL_3(R)/Λ` is a countable union, over `λ ∈ Λ ∖ {1}`, of
   cosets of proper centralizers. This is a Haar-null set. The argument is elementary and needs no claim.
2. **Mixing.** `SL_3(R)` acts transitively, hence ergodically, on `SL_3(R)/Λ`. It has the Howe--Moore
   property (`howe-moore-property-for-simple-lie-and-p-adic-groups`), so the Koopman coefficients on
   `L²_0` are `C_0` on `SL_3(R)`, and they tend to `0` along the discrete subgroup `SL_3(Z)`.
3. **Sofic group.** `SL_3(Z)` is residually finite, hence sofic.
4. **Not sofic** by hypothesis.
