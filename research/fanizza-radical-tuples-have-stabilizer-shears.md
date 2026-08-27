---
rg: 2
id: fanizza-radical-tuples-have-stabilizer-shears
kind: claim
title: The two Fanizza endpoint tuples have exact all-sector S3 stabilizer alignments
artifacts:
  - experiments/cross_context_radical_relator_audit.py
  - research/artifacts/cross-context-radical-relator-audit-2026-08-23.md
distinct_from:
  covariant-model-satisfies-cross-context-radical-relators: that must choose the three complete context-transport unitaries simultaneously in the amplified HALT model; this closes the full finite packet and satisfying-sector obstruction which those choices must respect.
  fanizza-radical-charts-admit-common-symplectic-reset-subgroups: that finds independent nondegenerate complements for the three odd chart forms; this chooses the complements equivariantly and fixes all designated outside words, not only the overlap type.
  s3-equivariant-affine-clifford-return-edge: that seeks one generated S3-semidirect edge carrying the reset residual and fresh endpoint semantics; this is the exact old-chart Clifford conjugacy calculation for the two named raw-word tuples.
---

Let the two outer coordinates of the predicate compiler be `e_0,e_1`, put

```text
r_(a,0)=e_0 tensor k_a,       r_(a,1)=e_1 tensor k_a,
ell_3=ell_1+ell_2,
```

and label the three endpoint charts

```text
alpha=ell_1,        beta=ell_3,        gamma=ell_2.       (XRS1)
```

There are two lifted `S_3=GL_2(F_2)` involutions `s_0,s_1` such that

```text
s_0 tau_(ell_1) s_0^(-1)=tau_(ell_3),
s_0(r_(a,0))=r_(a,0)                    for every a,

s_1 tau_(ell_3) s_1^(-1)=tau_(ell_2),
s_1(r_(a,1))=r_(a,1)                    for every a.       (XRS2)
```

The equalities in `(XRS2)` are exact packet-word equalities.  No central
fourth-root phase occurs.  Moreover the reset hyperplanes may be chosen so
that `s_0(W_alpha)=W_beta` and `s_1(W_beta)=W_gamma`.  These are identities of
the full affine alternating pencils, so they hold on every selector sector,
including every satisfying sector where the raw words are noncentral.

On each shared-overlap isotypic block, project an outside word along the
one-dimensional radical onto the chosen nondegenerate hyperplane.  For either
comparison in `(XRS2)`, the projected vectors indexed by all marked atoms are
linearly independent and isotropic, and the relevant shear sends the source
tuple to the target tuple entry by entry.  Consequently their linear-relation
spaces, symplectic Gram matrices, and joint Pauli spectral multiplicities
agree.  The prescribed twist-functional differences are all zero:

```text
(ell_1-ell_3)(r_(a,0))=0,
(ell_3-ell_2)(r_(a,1))=0.                                (XRS3)
```

The executable certificate checks the four fixed Fanizza predicates, all
eight marked atoms, both comparisons in all selector sectors: 80 comparison
blocks in total, of which 64 are satisfying blocks.  It also checks 144
individual central-twist evaluations.

This removes the former satisfying-sector spectral/conjugacy risk from the
cross-context-relator completeness problem.  It does not assert that two
independent raw coordinates lie in one reset multiplicity commutant; the
separate claim
`two-raw-radicals-fail-common-symplectic-reset`
shows that stronger statement is false.
