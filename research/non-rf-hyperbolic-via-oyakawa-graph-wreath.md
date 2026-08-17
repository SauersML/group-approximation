---
rg: 2
id: non-rf-hyperbolic-via-oyakawa-graph-wreath
kind: route
title: Look for the counterexample among Oyakawa's new hyperbolic graph-wreath products
target: non-residually-finite-hyperbolic-group
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

The most attractive route on the list, because it needs no new construction
and the construction it uses is new.  Oyakawa's Corollary 1.4 produces
hyperbolic groups `X(H) ⋊ G` from a proper cocompact action on a locally
finite hyperbolic graph of girth `> 20` with finite lamp group `H`.  These
groups postdate every no-go in this repository, they are lamp-shaped rather
than lattice-shaped, and their author explicitly suggests that their residual
finiteness might bear on the open problem.  So: find one that is not
residually finite.

Dead: by `oyakawa-graph-wreath-rf-iff-acting-group-rf` the product is
residually finite exactly when `G` is, and `G` is itself hyperbolic under
those hypotheses.  Any failure in the family is inherited from a hyperbolic
group that already had it, so the family cannot contain the *first*
counterexample.  The graph-wreath construction turns out to be transparent to
residual finiteness — which is a real answer to Oyakawa's question, just not
the answer one hoped for.

**What survives the demolition.**  The relative construction (Oyakawa's
Theorem 1.3) is untouched: there the action is on a fine rather than locally
finite graph and vertex stabilizers are only finitely generated, so both
finiteness inputs of the proof fail and the criterion is not discharged.  A
live attack would have to make Needham's separation conditions fail for that
action *while* keeping every Oyakawa peripheral residually finite, and then
fill via `non-rf-hyperbolic-via-relative-dehn-filling`.  Failing Needham's
conditions is itself a profinite-separability failure of the action, closely
related to residual finiteness of those same peripherals, so the two demands
pull against each other; no data satisfying both is known here.  That is a
different route, and it is not this one.
