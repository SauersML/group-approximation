---
rg: 2
id: near-representation-amenability-dichotomy
kind: claim
title: Every amenable near representation of a Kazhdan group has a positive-charge finite-dimensional sector
root: true
refuted_by: [kazhdan-rf-amenable-near-model-has-no-positive-finite-sector]
distinct_from:
  amenable-rep-of-kazhdan-has-fd-subrep: that is the genuine-representation existence theorem; the counterexample here explains why bare existence cannot be upgraded to positive invariant charge.
  bekka-valette-amenable-t-dichotomy: that is the published genuine-representation dichotomy; this attempted a stronger charge-visible conclusion.
  wreath-flexible-hs-stability: that asks whether almost-representations are close to genuine ones in normalized Hilbert--Schmidt norm; the failure here already occurs for a genuine representation.
---

**REFUTED.**  The precise finite-dimensional claim in the title is false.
The former alternative wording with an unrestricted “invariant sector” was
ill-posed.

The proposed claim asked whether every amenable near representation of a
property-(T) group has a finite-dimensional invariant subspace of positive
charge.  The answer is no.
[[kazhdan-rf-amenable-near-model-has-no-positive-finite-sector]] constructs an
essentially free amenable **genuine** representation of an infinite residually
finite Kazhdan group in which every finite-rank projection has charge zero.
Exact representations are near representations, so this is already a
counterexample.

If arbitrary invariant projections are allowed, the assertion has no content:
the identity projection is invariant and has charge one. Requiring merely a
proper invariant projection does not repair it in the block-ultralimit model,
because deleting finitely many invariant blocks gives a proper invariant
projection of charge one.

Bekka--Valette and [[amenable-rep-of-kazhdan-has-fd-subrep]] remain perfectly
consistent with the counterexample. They provide a nonzero finite-dimensional
subrepresentation, not positive mass for an independently chosen finitely
additive charge.

A meaningful replacement would have to specify a nonvacuous projection class,
an approximation scale, and a quantitative charge bound. No such replacement
is asserted here. This refutes the proposed Bekka--Valette shortcut.  It does not invalidate
[[amenable-charge-route]], whose Kahl--Schneider reduction remains a valid
open route.
