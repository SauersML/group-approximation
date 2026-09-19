---
rg: 2
id: countable-group-mf-conventions-proof
kind: route
title: Polar correction, local normalization, and representation-field implications
target: countable-group-mf-conventions
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/ManuscriptExactWrappers.lean
  - GroupApproximation/Sofic/MFRepresentationVariants.lean
---

## Direct proof

Polar correction identifies unitary classes in the genuine C-star quotient
with the quotient of unitary sequences, so faithful representations in the
two coronas are equivalent.  Local normalization turns the latter condition
into operator-norm local models with separation constant one.  Repeating
coordinates and amplifying blocks replaces arbitrary positive dimensions by
a strictly increasing sequence without changing the quotient representation.

For the stronger representation-field conventions, a genuine
finite-dimensional representation is already exactly multiplicative.
Reduced-norm convergence supplies the required separation, hence a PMatF
approximation is an operator-MF approximation.  Forgetting, in turn, the
permutation data, trace convergence, or finite-image condition proves the
implications from trace-free PPermF, trace-PMF, PFF, and PPF.  These are the
formal implications assembled by `manuscriptMFDefinitionEquivalences` and
`MFRepresentationVariants`.
