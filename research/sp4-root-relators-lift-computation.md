---
rg: 2
id: sp4-root-relators-lift-computation
kind: route
title: Enumerate Cayley-ball relators and integrate the determinant phase of the polar unitary part along one-parameter paths
target: sp4-root-relators-below-length-twelve-lift-to-universal-cover
requires: []
artifacts:
  - research/artifacts/maslov-mod3-sector-numerics-2026-09-05.md
  - experiments/maslov_sector/presentation.py
  - experiments/maslov_sector/lift_lattice_check.py
  - experiments/maslov_sector/RESULTS.txt
---

Breadth-first search to radius `6` over the sixteen letters `x_alpha(+-1)`
enumerates `1,148,696` elements of `Sp_4(Z)`; each non-tree edge gives a
closed loop, and after free and cyclic reduction and identification up to
rotation and inversion `304,412` relators of length at most `13` remain, all
checked to evaluate to the identity.  Every closed loop of length at most
`11` lies in the radius-5 ball and is a product of fundamental cycles of the
tree, all of which are recorded, so clause 1 is exhaustive.

For each relator the concatenated path `g(t)` of one-parameter subgroups
`x_alpha(+-t)` is a loop in `Sp_4(R)`; its class in `pi_1(Sp_4(R)) = Z` is
read off as the winding number of `det(P + iQ)` where
`g(g^T g)^{-1/2} = [[P,Q],[-Q,P]]` is the polar unitary part, because
`U(2)` is a deformation retract of `Sp_4(R)` and the determinant is an
isomorphism on `pi_1`.  The exponent of `zeta` in the lift of the relator to
`Sp~_4(Z)` is exactly this winding number, since the generators are lifted
along their own paths.  The computation is vectorized over relators and
returns integers to `2e-15`; the sanity values `w_alpha^4 -> 1` for long
roots and `0` for short roots agree with the known degrees of the root
`SL_2`'s on `pi_1`.

Clause 3 is an integer echelon reduction of the exponent-sum lattice with
the lift column (`lift_lattice_check.py`).
