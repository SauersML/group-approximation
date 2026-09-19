---
rg: 2
id: schur-violation-density-is-in-the-spin-commutant
kind: claim
title: Schur violation density lives in the selector multiplicity algebra, not the Clifford spin factor
distinct_from:
  schur-predicate-is-character-density-difference: that identifies the density element exactly; this locates that element in the spin/multiplicity tensor decomposition and rules out a proposed mixing argument.
  normalizer-multiplicity-twist-breaks-prefix-expander-rounding: that concerns extra action of Clifford normalizers; this obstruction remains even for ideal spin-only expander unitaries.
---

In an exact `J=-1` representation of the Schur baseline packet `A_f`, decompose
over selector characters:

```text
H=directSum_(x in F_2^k) (S_x tensor M_x),
dim(S_x)=D,
A_f''=directSum_x (M_D tensor I_(M_x)).                         (SVC1)
```

The forbidden predicate projection and character-density gap are

```text
P_f=directSum_x f(x)(I_D tensor I_(M_x)),
Z_(C_f)-Z_(B_f)=P_f/(2D).                                      (SVC2)
```

Thus they lie in the commutant of every Clifford spin block.  A quantum
expander acting on the `M_D` coordinates fixes `(SVC2)` pointwise and cannot
decorrelate it from a sibling selector observable.  Two copies of `(SVC2)`
may be perfectly correlated on the common multiplicity algebra while all
spin-expander commutators vanish.

Consequently the Schur violation observable cannot be substituted for the
spin-factor variable `x` in `(ESF1)`.  The route
The archived subtree-independence route incorrectly inferred the
predicate covariance estimate from spin-factor placement alone and is
invalidated.  A valid tree return must first **consume or reset the old
selector character** and transport the branch multiplicity into a new chart;
this is exactly the separate renewal requirement, not an expander corollary.
