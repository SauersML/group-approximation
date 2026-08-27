---
rg: 2
id: literal-reduced-group-algebra-proof
kind: route
title: Pass the literal group obstruction to its reduced C-star algebra
target: literal-stably-finite-non-mf-reduced-group-algebra
requires: [literal-central-mark-corona-invisible]
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_IMPACT_FORMAL_STATUS.md
  - GroupApproximation/Sofic/LiteralNonMFEndpoint.lean
  - GroupApproximation/Analysis/ReducedGroupCStarSeparable.lean
  - GroupApproximation/Analysis/ReducedGroupCStarTraceFaithful.lean
---

## Why sufficient

The reduced algebra is separable because `E` is countable.  Its canonical
coefficient-at-one trace is faithful: right translations commute with the
reduced algebra and propagate vanishing from the identity vector to the
standard basis.  The normalized matrix traces remain faithful, so every
isometry in every nonempty finite matrix amplification is unitary.  Finally,
an MF embedding of the reduced algebra would restrict to a faithful corona
representation of the canonical group unitaries, contradicting
`literal-central-mark-corona-invisible`.  The conjunction is exposed by
`manuscriptTheoremD`.
