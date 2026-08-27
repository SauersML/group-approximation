---
rg: 2
id: sp4-global-affine-subgroup-exclusion-proof
kind: route
title: Force the affine normal lattice into a rational symplectic parabolic
target: sp4-contains-no-isw-affine-subgroup
requires:
  - sp4-maximal-parabolics-contain-no-isw-affine-subgroup
---

Apply multiplicative Jordan decomposition to the normal abelian subgroup.
A finite-index subgroup of the free actor centralizes the diagonalizable
closure of its semisimple parts.  A hyperbolic actor then kills those
semisimple parts on a finite-index characteristic sublattice, leaving a
nontrivial rational unipotent closure `U`.

The common fixed space of `U` in the natural four-dimensional symplectic
module forces `N(U)` into a proper rational parabolic.  The only apparently
exceptional case, a symplectic two-dimensional fixed space, would make the
nontrivial unipotent action on its symplectic complement acquire an
additional fixed vector, contradicting the definition of the full common
fixed space.  Rational conjugacy and arithmetic commensurability then reduce
to the already established integral Klingen/Siegel parabolic exclusion.
