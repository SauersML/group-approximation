---
rg: 2
id: deligne-triple-cover-via-deligne-lattice-non-mf
kind: route
title: Exclude the full parameter circle by non-MF of Deligne's lattice and the finite branch by period arithmetic
target: deligne-triple-cover-exact-mf-radical
requires:
  - deligne-universal-cover-lattice-is-not-mf
  - deligne-lattice-non-mf-forces-finite-parameter-group
  - deligne-finite-parameter-group-has-period-prime-to-three
  - deligne-sep7-all-cover-mf-radical-classification
---

The argument has three steps.
1. By item 1 of `deligne-lattice-non-mf-forces-finite-parameter-group`, the first prerequisite gives
   `P_op = (1/m)Z/Z` for one even `m`. The reason: a single irrational norm-parameter glued to the residually finite
   base gives an injective corona model of the lattice.
2. The third prerequisite gives `3 not | m`. So neither `1/3` nor `2/3` lies in `P_op`.
3. The annihilator formula of `deligne-sep7-all-cover-mf-radical-classification` at covering degree three makes
   `Rad_MF(E_3)` the whole order-three kernel.

**Difference from `deligne-triple-cover-via-winding-deficit` and `deligne-triple-cover-via-sublinear-windings`.**
Those routes exclude the full circle through a quantitative statement about quasi-representations of `Sp_4(Z)`. This
route excludes it through a qualitative, parameter-free statement about one Kazhdan lattice.

Under the instance `(CPE*)` of `commutant-projection-extraction`, the first prerequisite is exactly equivalent to
finiteness of `P_op` (item 5 of the theorem). So it is then implied by the winding deficit, and it is necessary for
the flagship.

**Each prerequisite can fail on its own.**
- Non-MF of the lattice fails through an injective corona model of `Gamma~`. If `P_op` is finite, such a model must
  carry an arc of central spectrum (item 4 of the theorem).
- The period statement fails through an MF model of `E_6`.
