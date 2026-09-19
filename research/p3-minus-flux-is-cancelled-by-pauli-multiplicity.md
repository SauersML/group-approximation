---
rg: 2
id: p3-minus-flux-is-cancelled-by-pauli-multiplicity
kind: claim
title: A p-three minus flux is exactly cancelled by a two-dimensional Pauli multiplicity gauge
distinct_from:
  fixed-shift-invariance-does-not-force-flat-profile: that invalidates the scalar depth-profile step; this gives a finite-dimensional exact escape from the later metaplectic-flux step itself.
  source-hecke-data-leave-projective-square-free: that varies one projective coefficient by external tensor factors; this cancels the specific minus-one oscillator holonomy while preserving the native Heisenberg covariance.
  two-untwisted-field-matchings-force-complete-cross-commutation: that uses finite Heisenberg uniqueness to eliminate multiplicity freedom after additional field relations; this proves that Stone--von Neumann uniqueness alone leaves exactly enough multiplicity freedom to absorb the p-three sign.
---

Let `pi` be a finite Heisenberg/oscillator packet and suppose two canonical
transport operators `A,B` implement the two coweight automorphisms on the
packet with scalar holonomy

```text
AB=-BA.                                                  (PMG1)
```

On the doubled packet put

```text
pi'(g)=pi(g) tensor I_2,
A'=A tensor X,
B'=B tensor Z,                                          (PMG2)
```

where `X,Z` are the Pauli involutions.  Since `XZ=-ZX`, one has

```text
A'B'=B'A'.                                              (PMG3)
```

Every Heisenberg covariance equation remains exact because the Pauli
factors commute with `pi'(g)`.  Thus the minus-one scalar flux is not a
finite-dimensional contradiction: an even multiplicity sector absorbs it
with zero normalized-HS defect and no trace dilution.

The construction applies blockwise to arbitrary even multiplicity and to a
positive direct-sum fraction of a model.  It does not claim to satisfy the
full `SL_3(Z/3^a)` parahoric/Weyl interlock.  Rather, it proves that the
Stone--von Neumann statement "the oscillator intertwiner is unique up to
multiplicity unitary" is insufficient for the p-three closure.  The needed
dictionary theorem must show that the additional parahoric relations force
the multiplicity holonomy to be trivial (or quantitatively far from the
Pauli projective class).  Merely identifying the scalar oscillator factor
with `(3,3)_3=-1` does not do so.
