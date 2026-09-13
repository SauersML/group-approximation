---
rg: 2
id: sl3z-dense-with-unipotent-lattice-has-finite-index
kind: claim
title: A Zariski-dense subgroup of SL_3(Z) containing a lattice of a maximal parabolic unipotent radical has finite index
---

Let `N <= SL_3(Z)` be Zariski dense in `SL_3`. Suppose `N` contains a
finite-index subgroup of `U(Z)`, where `U` is the unipotent radical of the
stabilizer of a rational plane or of a rational line in `Q^3`. Then `N` has
finite index in `SL_3(Z)`.

This is the `SL_3` case of Venkataramana's theorem on Zariski-dense subgroups
of arithmetic groups (J. Algebra, 1987, recalled, not re-read). The route
`sl3z-dense-with-unipotent-lattice-has-finite-index-proof` gives a
self-contained reduction to the finite-index statement
`sl3z-congruence-elementary-generators-have-finite-index`.

**Consequences for Serre's question.**

- Any finitely generated, not finitely presented subgroup `N <= SL_3(Z)` is
  thin (`non-zariski-dense-subgroups-of-sl3z-are-coherent`). So it meets every such
  `U(Z)` in a subgroup of rank at most one.
- `N` contains no finite-index subgroup of any rational conjugate of the
  integral Heisenberg group, since that group contains `U(Z)` for
  `U = {I + v e_3^T : v in span(e_1, e_2)}`.
- Every finitely generated subgroup of `SL_3(Z)` containing a finite-index
  subgroup of some such `U(Z)` is finitely presented.
