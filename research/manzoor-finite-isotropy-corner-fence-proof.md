---
rg: 2
id: manzoor-finite-isotropy-corner-fence-proof
kind: route
title: Use torsion-freeness and absence of invariant vectors in an infinite regular representation
target: manzoor-isotropy-has-no-positive-finite-type-corner
requires:
  - finite-isotropy-relation-is-central-corner
  - non-cohyperlinear-irs-exists
---

Every finite subgroup of a free group is trivial.  If the Manzoor stabilizer
were finite on a positive-measure set, ergodicity of the IRS and invariance of
stabilizer cardinality would make it trivial almost surely.  Its character
would then be the regular character `delta_e`, whose GNS algebra is `L(F)` and
is Connes embeddable.  This contradicts non-cohyperlinearity.  The stabilizer
is therefore infinite almost surely.

For an infinite discrete group `H`, an invariant vector in its left regular
representation would be a square-summable function constant on `H`, hence
zero.  Equivalently the trivial representation is not a normal summand of
`L(H)`.  A finite subgroup averaging projection has range consisting of
vectors constant only on its finite cosets; requiring invariance under the
whole infinite stabilizer again forces a constant square-summable function
and gives zero.  Therefore no positive finite subgroup-type projection can
select the trivial representation of the actual stabilizer.  The positive
corner theorem cannot apply to the Manzoor source.

