---
rg: 2
id: cdi-wreath-projective-gate-transfer-proof
kind: route
title: Read the tensor coefficient and crossed-product Fourier coordinate in CDI Proposition 3.8
target: cdi-wreath-extension-preserves-projective-basis-gate
requires:
  - cdi-property-t-envelope-has-nonabelian-base
  - projective-basis-character-criterion
---

CDI Proposition 3.8 gives formula `(CDI-P1)` verbatim.  The canonical trace
of a cocycle crossed product vanishes on every nonidentity Fourier
coordinate, proving the first line of `(CDI-P2)`.  On the identity coordinate
the trace is the tensor-product trace, proving the product formula.

An element with `b!=e` cannot be scalar because it belongs to the `b` Fourier
coordinate whereas scalars belong to the identity coordinate.  For a
finite-support base element, suppose

```text
tensor_d pi(x_d)=lambda 1.
```

Conjugation by the tensor is trivial.  Applying it to an operator supported
in one coordinate shows that `Ad(pi(x_d))` is trivial on the factor `M`, so
`pi(x_d)` is scalar.  Conversely a tensor of scalars is scalar.  This proves
the scalar-kernel description.

If `chi_A` vanishes off its scalar kernel, every nonscalar base tensor has a
nonscalar coordinate and one factor in `(CDI-P2)` vanishes; outer Fourier
coordinates also vanish.  Hence `chi_G` has the same property.  Conversely,
put any `a in A` at one site and identities elsewhere.  Its scalarity and
trace are exactly those of `pi(a)`, so vanishing for `chi_G` implies
vanishing for `chi_A`.  This proves `(CDI-P3)`.

For scalar phases, the slice argument says every scalar tensor has scalar
coordinates, so its phase is a finite product of elements of `S_A`, still in
the subgroup `S_A`.  Single-site tensors give the reverse inclusion.  Thus
`S_G=S_A`.  A finite scalar phase group makes the section cocycle
finite-valued; a trivial one makes the projective quotient representation
honest.  Finally CDI's Lemma 5.1 (the Ge--Popa generator lemma) supplies only
three generating unitaries and imposes none of these coefficient conditions,
so no further verdict follows from the source.

Primary source: Chifan--Drimbe--Ioana,
[*Embedding universality for II1 factors with property (T)*](https://arxiv.org/abs/2205.07442),
Proposition 3.8 and Lemma 5.1.

For the group-factor specialization `(CDI-P4)`, the first formula in
`(CDI-P2)` is the regular character of `G`; regularity makes the extended
homomorphism faithful, and generation in Proposition 3.8 identifies its
factor with `L(G)`.  For `(CDI-P6)--(CDI-P8)`, the honest central-extension
representation has scalar kernel exactly `S` and vanishes elsewhere.
Applying the already proved scalar-kernel and phase-group calculations shows
that the output is a twisted group factor with the same phase group `S`.
When `S` is finite, the usual central-character idempotent in the final
central extension has canonical trace `1/|S|`; this is one global projection,
not an infinite product of coordinate projections.  This proves the positive
specialization added to the claim.
