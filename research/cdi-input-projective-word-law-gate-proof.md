---
rg: 2
id: cdi-input-projective-word-law-gate-proof
kind: route
title: Apply the intrinsic projective-word characterization and audit the two source constructions
target: cdi-input-projective-word-law-remains-a-group-factor-gate
requires:
  - projective-word-law-characterizes-twisted-group-factors
  - non-ce-property-t-equivalence-relation-exists
  - cdi-standard-generator-choice-fails-projective-gate
---

Both `N` and `M_tilde` are finite factors with separable predual, so
`projective-word-law-characterizes-twisted-group-factors` applies verbatim
and proves the displayed equivalence for each.

The established construction of `N` passes through an IRS/relation GNS
algebra and then a property-`(T)` relation envelope.  Its output is an
inclusion of tracial von Neumann algebras, not a multiplication-closed
orthonormal unitary basis.  No step asserts that the relation factor is a
twisted group factor.  The CDI source itself distinguishes its universal
property-`(T)` factors from group factors in Remark 1.1.

For `M_tilde`, CDI Lemma 5.1 supplies a particular three-unitary generating
format.  `cdi-standard-generator-choice-fails-projective-gate` gives a fully
allowed implementation of that format with a word of strictly intermediate
trace, proving only that this tuple fails.  The intrinsic characterization
shows why no conclusion about another tuple follows: ruling out every tuple
is exactly proving that `M_tilde` is not isomorphic to any twisted group
factor, a theorem absent from both sources.

Finally, a finite phase group turns the twisted factor into a positive
central corner of its finite central extension.  Non-CE of `X` then forces
that extension group to be non-hyperlinear.  This is the stated conditional
compiler and isolates finite phase as an additional requirement beyond
`(CDI-I1)`.

