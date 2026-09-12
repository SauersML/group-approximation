---
rg: 2
id: nonrf-hyperbolic-group-with-torsion-free-residual
kind: claim
title: A non-residually-finite hyperbolic group whose finite residual is torsion-free
distinct_from:
  non-residually-finite-hyperbolic-group: that allows invisible torsion; this demands a nontrivial torsion-free finite residual, which makes the group virtually torsion-free, and is equivalent to a torsion-free counterexample rather than to an arbitrary one
  hyperbolic-group-trivial-radical-residual-prime-torsion: that is the shape with prime torsion in the residual, into which every counterexample converts; this is the opposite shape, with no torsion in the residual, and no conversion into it is known
---

Exhibit a word-hyperbolic group `G` with `R_f(G) != 1` and `R_f(G)`
torsion-free.

By the finite torsion-carrier criterion such a `G` is virtually torsion-free,
so this claim is equivalent to
`torsion-free-non-residually-finite-hyperbolic-group`.

## Attempts

- **Case B of the filling proof.**  The counterexamples handled by Case B of
  `hyperbolic-rf-question-equals-vtf-question-proof` are exactly of this shape.
  Case A counterexamples are not, and the free-factor shape never is.
- **No known conversion from Case A.**  Dehn fillings add torsion; Olshanskii
  quotients preserve conjugacy classes of finite-order elements (clause 7 of
  the theorem quoted in `olshanskii-g-subgroup-quotient-citation`); overgroups
  contain the old torsion; and invisibility does not pull back along
  surjections.  So none of the repository's transfer tools turns invisible
  torsion into a torsion-free residual.
