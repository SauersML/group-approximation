---
rg: 2
id: mipstar-effective-projective-basis-audit-proof
kind: route
title: Compare the source outputs with the affine native-basis criterion
target: mipstar-does-not-supply-effective-projective-basis
requires:
  - explicit-commuting-operator-separating-game
  - mipstar-bcs-tracial-nonru-exists
  - non-ce-trace-on-sofic-racg
  - twisted-group-basis-forces-affine-context-support
---

The first two bullets are the literal outputs recorded from JNVWY Theorem
12.13 and Paddock--Slofstra Example 4.2.  The RACG pullback and its non-CE
character are exactly `non-ce-trace-on-sofic-racg`.

If the source observables were native elements of a projective group basis,
the established affine-support theorem would replace each occupied support by
an affine slice while retaining the tracial representation.  A successful
finite-dimensional approximation of the projective trace would likewise
approximate those affine relations.  This is the LCS separation that
Paddock--Slofstra Proposition 5.8 identifies with a finitely presented
nonhyperlinear solution group.  Neither cited source proves this native-basis
premise or supplies the resulting affine slices.

The source papers do not propose a different projective basis or enumerate a
scalar word kernel.  Thus their established conclusions stop strictly before
the effective twisted-factor gate; the statement makes no invariant claim
that a different basis cannot exist.
