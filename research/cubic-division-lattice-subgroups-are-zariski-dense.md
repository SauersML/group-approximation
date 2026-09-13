---
rg: 2
id: cubic-division-lattice-subgroups-are-zariski-dense
kind: claim
title: Every nonamenable subgroup of SL_1(O_D), D a cubic division algebra over Q, is Zariski dense
artifacts:
  - research/artifacts/sl3z-invariant-vector-witnesses-2026-09-12.md
---

ESTABLISHED (unreviewed).  Let `D` be a central division algebra of degree 3
over `Q`, `O_D` a maximal order and `Gamma_D = SL_1(O_D)`.  `Gamma_D` is a
cocompact lattice in `SL_1(D (x) R) = SL_3(R)`, so it is an infinite Kazhdan
group.  Every nonamenable subgroup `H <= Gamma_D` is Zariski dense in
`SL_1(D)`.

Consequence.  By strong approximation for finitely generated Zariski-dense
subgroups, for every finite family of nonamenable subgroups of `Gamma_D` and
all but finitely many primes `p`, each subgroup maps onto
`SL_1(O_D/pO_D) = SL_3(F_p)`.  Hence no nontrivial irreducible representation
of `Gamma_D` through such a congruence quotient has a vector fixed by any of
them: invariant-vector witnesses in the sense of
`sl3z-has-no-invariant-vector-witnesses` cannot exist at large levels, and
`Gamma_D` has no nonamenable subgroup that is a block `SL_2` or an `SO_3` even
rationally.
