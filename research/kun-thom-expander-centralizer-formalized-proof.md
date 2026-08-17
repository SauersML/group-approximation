---
rg: 2
id: kun-thom-expander-centralizer-formalized-proof
kind: route
title: Correlate the diagonal against the Kazhdan pair, then repair to an exact expander
target: kun-thom-expander-centralizer-formalized
requires: []
artifacts:
  - GroupApproximation/KunThom/KunThomTheorem.lean
  - GroupApproximation/KunThom/KunThomCorrelation.lean
  - GroupApproximation/KunThom/KunThomDiagonal.lean
  - GroupApproximation/KunThom/KunThomRounding.lean
  - GroupApproximation/KunThom/KunThomFiniteMarkov.lean
  - GroupApproximation/KunThom/KunThomEssential.lean
---

## Direct proof, machine-checked

**Parameters first.**  `exists_improvementParameters` derives every constant
from the Kazhdan factor and the Cheeger bound, so nothing downstream has to
guess an order of quantifiers; `kazhdanFactor_nonneg_lt_one` is what keeps the
factor in `(0,1)`.

**The relation.**  `exists_pairProduct_relation_eventually` produces, eventually
along the approximation, the almost-multiplicativity relation the argument runs
on, in the `MultiplicativeApproximation` form.  `KunThomCorrelation` and
`KunThomDiagonal` are where the second factor is pushed against the first: a
`J`-element commuting with all of `K` must almost preserve the `K`-orbit
structure, and expansion of the `K`-labelled graph turns "almost preserves"
into "preserves outside a negligible set" -- this is the step that fails for a
union of expanders, since a commuting element may permute components.

**From Cheeger to scale.**  `directedExpansionAtScale_of_cheeger` converts the
Cheeger lower bound into expansion at the cluster scale, using
`A.card_tendsToInfinity` to discard small models, and
`firstFactorLabels_injective_eventually` to know the labels separate.

**Rounding out.**  `KunThomRounding` and `KunThomFiniteMarkov` turn the
resulting almost-action into an exact finite one on a single component, which
is a finite-group statement; that is the LEF witness for `J`, and
`repairBudget_le_three_symmDiff` is the accounting that keeps the repair
within budget.

`KunThomEssential.isLEF_of_matchingCertificate` wraps this for the caller:
`repairedApproximation C` is the repaired approximation and
`repairedDirected_expands_eventually` discharges the Cheeger hypothesis, so a
matching certificate plus Kazhdan-pair data is all a consumer must supply.
