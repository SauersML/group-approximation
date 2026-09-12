---
rg: 2
id: torsion-dense-twisted-factor-compiler-proof
kind: route
title: Approximate the multiplier class and diagonalize twisted microstates
target: torsion-dense-schur-multiplier-compiles-twisted-nonce
requires:
  - thom-central-corner-criterion
---

Because `T` is divisible, it is an injective `Z`-module, so the Ext term in
the universal coefficient theorem vanishes and gives `(TDS1)`.  For
countable `Gamma`, cocycles form a compact metrizable subgroup of
`T^(Gamma x Gamma)`, coboundaries form a compact (hence closed) subgroup, and
the quotient topology on `H^2` agrees with the compact topology on
`Hom(A,T)`.

Pontryagin duality gives the density statement.  Torsion points of
`Hom(A,T)` are exactly finite-image characters.  The annihilator of their
closure consists of elements of `A` killed by every finite-image character,
which is exactly `R_fin(A)`.  Taking annihilators again proves `(TDS2)`.

Choose torsion classes `[theta_n]->[omega]`.  After multiplying cocycle
representatives by coboundaries, choose representatives `eta_n` converging
pointwise to `omega`.  Each `eta_n` is cohomologous to a finite-valued
cocycle because its class is torsion, so `L_(eta_n)(Gamma)` is
trace-isomorphic to a finite central sector.

Suppose every torsion twist were CE.  Fix a finite set of group elements and
a microstate tolerance for `L_omega(Gamma)`.  For large `n`, the finitely
many scalar multiplication constants of `eta_n` on that set are as close as
desired to those of `omega`.  A matrix microstate for the canonical
unitaries of `L_(eta_n)(Gamma)` then satisfies the `omega`-twisted products
and canonical delta moments with the prescribed tolerance.  Diagonalizing
over finite sets and tolerances gives microstates for `L_omega(Gamma)`, a
contradiction.  Hence some torsion twist is non-CE.

Rephase that torsion cocycle to `mu_m` values.  Its twisted factor is the
central-character corner of the finite central extension by `mu_m`; a CE
group factor has only CE positive corners, so the extension is
non-hyperlinear.

Finally, a finitely presented group is of type `FP_2`.  Tensoring a partial
finite projective resolution with the trivial module shows `H_2(Gamma,Z)` is
a subquotient of a finitely generated abelian group, hence finitely
generated and residually finite.
