---
rg: 2
id: transient-crossed-products-have-nonsimple-mf-quotients-proof
kind: route
title: A transient point makes the core non-minimal, and a proper invariant closed subset gives a noncentral proper normal subgroup
target: transient-crossed-products-have-nonsimple-mf-quotients
requires:
  - chain-transitive-core-has-no-transient-points
  - zero-dimensional-system-mf-radical-is-core-restriction
artifacts:
  - research/artifacts/un-hh-extension-toeplitz-subshift-2026-09-13.md
---

- **Quotient.** By the core-restriction theorem, the maximal MF quotient is `EL_n(R_Y)` with `R_Y = LC(Y,F_2) x| Z`.
- **The core is not minimal.** Since `X != Y`, the Conley lemma shows `Y` is not chain transitive, hence not minimal.
  So `Y` contains a nonempty closed invariant `Z != Y`.
- **An ideal.** Let `I_Z` be the set of `sum f_j u^j` with every `f_j` vanishing on `Z`. It is a two-sided ideal. It is
  nonzero, since `Y \ Z` is open and nonempty in a zero-dimensional space, so contains a nonempty clopen `U` of `Y` with
  `chi_U in I_Z`. It is proper, since `1` is not in `I_Z`.
- **A normal subgroup.** For `n >= 3`, `EL_n(R_Y, I_Z)` is normal.
  - Nontrivial: `[e_12(a), e_23(1)] = e_13(a) != 1` for `a in I_Z` nonzero.
  - Noncentral: `[e_13(a), e_32(1)] = e_12(a) != 1`, so `e_13(a)` is not central.
  - Proper modulo the centre: `EL_n(R_Y)` maps onto `EL_n(R_Y/I_Z) != 1`, which is perfect for `n >= 3`. If
    `EL_n(R_Y, I_Z) Z` were all of `EL_n(R_Y)`, that image would be a quotient of the abelian `Z`.
- **Conclusion.** Its image is a proper nontrivial normal subgroup of `EL_n(R_Y)/Z`.
