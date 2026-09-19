---
rg: 2
id: berend-primitive-spectrum-stratification-proof
kind: route
title: Induce from one dense free orbit and classify every nonfaithful irreducible representation by finite orbit isotropy
target: berend-primitive-spectrum-has-one-faithful-generic-point
requires:
  - berend-proper-quotients-have-decomposition-rank-at-most-two
  - berend-torus-actions-give-strongly-qd-polycyclic-groups
artifacts:
  - research/artifacts/stw99-lxxxvi-berend-frontier-2026-08-30.md
---

Choose a nontorsion point `x in T^3`.  Its orbit is not finite and hence is
dense by the Berend dichotomy.  It is also free: if a nonidentity unit
fixed `x`, then `x` would lie in the finite kernel of the corresponding
nonzero integer endomorphism `u-1`, and would be torsion.

The regular orbit representation `pi_x` on `l^2(Z^2)` is faithful on
`C(T^3)`, because the orbit is dense, and therefore faithful on `A` by the
Archbold--Spielberg theorem used in Eckhardt's Lemma 2.2.  It is
irreducible.  Indeed the strong closure of the diagonal algebra
`pi_x(C(T^3))` is `l^infinity(Z^2)`: continuous functions separate every
finite collection of distinct orbit points, and bounded pointwise
interpolation converges strongly.  An operator commuting with this
diagonal algebra is diagonal, and commuting also with the translation
unitaries forces its diagonal to be constant.  Thus the commutant of
`pi_x(A)` is scalar.  This proves that `0 in Prim(A)`.

In the hull--kernel topology,

`closure({0}) = {P in Prim(A) : P contains 0} = Prim(A)`,        `(BSP1)`

so `0` is dense.  If `P != 0` is primitive, then `A/P` is a primitive
proper quotient.  By the finite-orbit reduction it factors through
`C(F) ⋊ Z^2` for finite invariant `F`.  An irreducible representation
selects one transitive orbit `O subset F`; the standard finite transitive
groupoid calculation identifies

`C(O) ⋊ Z^2 = M_{|O|}(C*(Stab(O)))`.                        `(BSP2)`

Irreducible representations of `(BSP2)` are evaluation at characters of
`Stab(O)` and have image `M_{|O|}(C)`.  Their kernels are maximal, hence
closed points of `Prim(A)`.  The hull of the kernel of the orbit quotient
is the closed copy of `dual(Stab(O)) = T^2`.  There are countably many
finite orbits, all consisting of torsion points, which proves `(BPS1)` and
also shows that no second point can be dense.
