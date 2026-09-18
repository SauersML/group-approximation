---
rg: 2
id: property-t-free-leavitt-via-el20-comparison
kind: route
title: Reduce the Kazhdan-free St20 goal to the Kazhdan-free EL20 goal through the Khanh comparison
target: property-t-free-leavitt-full-mf-radical
requires:
  - property-t-free-el20-full-mf-radical
  - leavitt-steinberg-map-iso-from-rank-three
---

By `leavitt-steinberg-map-iso-from-rank-three` (Khanh, Theorem 5.4), the
Steinberg map `St_20(R) -> GL_20(R)=EL_20(R)` is an isomorphism for
`R=L_(F_2)(1,2)`.  It sends `z=x_13(s_1t_1)` to `e_13(s_1t_1)`.  `Rad_MF` is
an isomorphism invariant, so `(EMF1)` of `property-t-free-el20-full-mf-radical`
gives `Rad_MF(St_20(R))=St_20(R)`.

Kazhdan hygiene: the comparison is proved from Steinberg-group criteria,
simple connectivity of a poset complex, and Voronetsky's refinement.  No
property (T), Kazhdan projection, or spectral-gap input occurs.  The EL20
goal already forbids (T) and every literature theorem, so the composite
proof is Kazhdan-free, with the Khanh import as its only literature input.

Consequence for the graph: the two Kazhdan-free goals concern the same
group.  The distinct_from note in `property-t-free-el20-full-mf-radical` says
the St20 version "must control its central Steinberg kernel".  That note is
obsolete, since the kernel is trivial.  The St20 goal differs only in
permitting literature imports, so every EL20 route also serves it through
this reduction.
