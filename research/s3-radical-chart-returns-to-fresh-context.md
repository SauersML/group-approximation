---
rg: 2
id: s3-radical-chart-returns-to-fresh-context
kind: claim
title: Return the uniform radical crossed-product chart to a fresh BCS context
distinct_from:
  three-radical-twist-crossed-products-have-uniform-scale: that constructs three conjugate fixed-scale finite charts and their exact restriction matrices; this must place their returned blocks on the next shared selector tuple without losing the marked carrier.
  hnn-selector-chart-transport-preserves-mark-and-types: that transports an already reset abelian selector chart; this must first turn the two crossed-product block types into that fresh chart.
---

Construct a finite amalgam/HNN incidence which takes the two
`M_(D_0)` types of each chart `(RTC3)` to the two input types of the next BCS
context, with the following properties.

1. The three conjugate incidences implement the contextual branch choices
   used by the rank-one `S3` failure inequality.
2. Their approximate type-vector transport loss is `O(sqrt(E))` by fixed
   finite-group overlap alignment.
3. Old context selectors are reset before the next context is installed, so
   no forbidden cross-context commutation is imposed.
4. The joint amalgam embeds the marked base group and therefore retains an
   exact representation separating its marked word.

## Attempts

- Conjugating only the three finite `R_i` charts is now exact, but it returns
  their two block labels to one another rather than to a fresh BCS selector
  tuple.
- `fanizza-radical-charts-admit-common-symplectic-reset-subgroups` now merges
  the two chart blocks into two copies of one full-matrix subgroup type for
  every fixed Fanizza predicate.  The selector center on that already-merged
  spin carrier is now renewed by
  `fresh-selector-renewal-after-symplectic-chart-reset`; together with the
  fixed overlap alignment this closes the finite return incidence.
- `selector-free-spin-reset-leaves-contexts-independent` computes the exact
  one-edge incidence after this merge.  Both restriction matrices are
  `[1 1]`, so sharing the spin packet and adjoining fresh selectors allows
  every old/fresh character pair.  The return therefore needs a two-cell that
  acts on the multiplicity commutant; no further ordinary reset edge can carry
  the contextual branch law.
- A plain finite graph of these incidences still has stationary
  representation-ring flows.  The established return must be inserted into
  the existing one-sided Toeplitz/Fanizza recurrence, where the factor-two
  violation ledger is contractive and polynomial transport losses are
  summable.
