---
rg: 2
id: sp4-parabolic-scalar-cohomology-fence-proof
kind: route
title: Compute the Levi-invariant second cohomology of the Siegel and Klingen radicals
target: isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals
requires:
  - sp4-maximal-parabolics-contain-no-isw-affine-subgroup
---

The universal coefficient theorem with divisible coefficients gives
`H^2(N,T)=Hom(H_2(N,Z),T)`.

For `N_S = Sym^2(Z^2) = Z^3`,

```text
H_2(N_S,Z) = exterior^2 Sym^2(Z^2).
```

After tensoring with `Q`, this is again the irreducible
three-dimensional `SL_2`-module (up to the determinant twist), so it has no
trivial quotient.  Hence its coinvariants under `SL_2(Z)` are finite, and
the invariant characters in `H^2(N_S,T)` form their finite Pontryagin dual.

For the integral Heisenberg group, the homology of its standard central
extension gives

```text
H_2(H_3(Z),Z) = Z^2,
```

with the standard Levi action.  Its rational coinvariants vanish, so again
the integral coinvariants, and therefore the invariant character group, are
finite.  Equivalently, the invariant alternating form on the abelianization
is killed by the transgression: it is precisely the class defining
`H_3(Z)`.

Restriction from the semidirect product lands in these invariant groups.
If `c_n -> 1` pointwise, then `[c_n|N_i] -> 0` in `H^2(N_i,T)` because for a
finitely generated group the scalar coboundaries form a compact, hence
closed, subgroup of the cocycles.  A convergent sequence in the finite
subgroup `(ISC1)` is eventually zero.  This contradicts condition (1) of
ISW Theorem A.

Primary source pin: Adrian Ioana, Pieter Spaas, and Matthew Wiersma,
*Cohomological obstructions to lifting properties for full group
C*-algebras*, GAFA 30 (2020), Theorem A and Corollary B.  Their Theorem A
requires (1) a non-coboundary restriction to the relative-`(T)` subgroup,
(2) pointwise convergence of scalar cocycles to `1`, and (3)
finite-dimensional projective realizations.  In their Section 3.2 the
standard example uses the invariant determinant cocycle
`c((x,y),(z,t))=xt-yz`; the calculation above shows exactly which part is
absent for both `Sp_4` radicals.
