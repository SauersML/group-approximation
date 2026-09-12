---
rg: 2
id: chord-regauging-is-relative-commutant-feasibility
kind: claim
title: Closing one marginal chord is a relative-commutant feasibility problem
distinct_from:
  sequential-marginal-holonomy-is-conditional-rank-matching: that treats one new marginal while one frozen family is fixed; this treats two endpoint regauges and characterizes when their two unitary orbits meet.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for every shared marginal in one corner; this isolates the exact operator-algebraic condition at one non-tree chord.
---

Let `A_0,A_1<=M_D(C)` be finite-dimensional abelian star algebras, and let
`X_i` be a self-adjoint involution commuting with `A_i`.  Write
`(e_(i,s))_s` for the minimal projections of `A_i`.  The following are
equivalent.

1. There are unitaries `U_i in A_i'` such that

   ```text
   U_0 X_0 U_0^*=U_1 X_1 U_1^*.                         (CRF1)
   ```

2. There is a self-adjoint involution

   ```text
   Z in A_0' intersect A_1'                              (CRF2)
   ```

   satisfying, for `i=0,1` and every `s`,

   ```text
   rank(e_(i,s)(1+Z)/2)=rank(e_(i,s)(1+X_i)/2),
   rank(e_(i,s)(1-Z)/2)=rank(e_(i,s)(1-X_i)/2).          (CRF3)
   ```

Thus the first cyclic signed-Hecke chord is exactly a common-relative-
commutant interpolation problem with two conditional rank tables.  Equality
of the unconditional ranks of `X_0` and `X_1` is necessary but is generally
far from sufficient.

In particular, if `A_0 vee A_1=M_D(C)`, then

```text
A_0' intersect A_1'=C I.
```

Only `Z=+I` or `Z=-I` can occur, so a nonscalar chord marginal cannot be
closed by separator-preserving endpoint regauges inside that root block.
Any successful signed-Hecke cycle construction must therefore arrange a
nontrivial common relative commutant in the block-escaping infinite corner,
not merely equal finite ranks at the two endpoints.

The same equivalence holds in a finite matrix corner `qMq`; ranks are then
taken on `qC^D`.  In a properly infinite exact witness, rank equalities may
be replaced by Murray--von Neumann equivalence inside the corresponding
relative-commutant blocks.  This is a completeness relaxation only: the
finite-matrix obstruction remains `(CRF2)--(CRF3)`.
