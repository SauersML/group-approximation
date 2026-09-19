---
title: STW XXII audit --- uncountable cofinite factorial bundles (2026-08-30)
---

## New theorem

The trace problem has a positive answer for every factorial tracially
complete bundle over a compact Hausdorff base with finitely many
nonisolated points.  Neither the base nor the algebra or its fibres need be
metrizable or separable.  The one-point compactification of a discrete set
of arbitrary cardinality is the core new case.

This strictly enlarges
`trace-problem-holds-over-convergent-sequence-boundaries`, whose base is
countable compact metric.  It is independent of the common-ambient
expectation presentation in
`stw22-expectation-fields-have-uniform-traces` and uses no property Gamma.

## Why the uncountable assembly is legitimate

There are two possible hidden countability failures; both disappear for a
cofinite limit.

1. A Radon measure on the open discrete stratum is the sum of its atoms.
   Inner regularity reduces its mass to finite subsets, so only countably
   many atoms can be nonzero.  There is no uncountable diffuse remainder on
   the discrete stratum.
2. A projection field with fibre traces tending to zero in the cofinite
   filter has countable support: for each `n`, only finitely many coordinates
   have trace at least `1/n`.  Hence it and every orthogonal partial-isometry
   copy are uniform `2`-limits of a sequence of finite central sums.  Net
   completeness and an unrestricted section-selection axiom are unnecessary.

At an isolated point `d`, the central corner `1_{d}M` is already complete in
its faithful tracial `2`-norm and therefore is the finite-factor fibre.  All
spectral projections and partial isometries used in the proof lie in this
corner; no pointwise element is assumed to possess an external lift.

## Disintegration boundary

The central measure splits into its discrete atoms and a possible mass at
the cofinite point.  Factoriality identifies every atomic corner trace.  A
trace supported at the cofinite point is then forced through the `2`-norm
fibre by arbitrarily many orthogonal copies of every small spectral cut.
This is exactly the step that the naive W*-bundle disintegration argument
cannot perform over a general base: there, pointwise copies need not assemble
continuously.  Cofinite convergence makes their support automatically
countable and supplies the assembly for free.

## Literature and scope

The supplied STW source states Problem XXII in full generality and cites the
positive CPoU/property-Gamma results of Carrión--Castillejos--Evington--Gabe--
Schafhauser--Tikuisis--White, *Tracially complete C*-algebras*,
arXiv:2310.20594.  A primary-source search through 30 August 2026 found no
statement removing countability and metrizability for finite-derived-set
bases.  This is recorded as a new repository theorem, not a claim of
literature priority.

The proof uses the finite-derived-set topology essentially.  At a limit
point of limit points, a small-cut field need not have countable or
cofinitely vanishing support, and independent fibrewise copies need not be
sections.  No conclusion is claimed for arbitrary scattered compacta or for
general Bauer boundaries.
