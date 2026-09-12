---
rg: 2
id: dinur-pcp-theorem-from-gap-amplification
kind: route
title: Iterate constant-factor UNSAT amplification and read the resulting gap CSP as a PCP
target: dinur-pcp-theorem
requires: [dinur-constraint-gap-amplification]
---

Start with graph 3-colorability.  Its inequality-edge constraint graph over
three colors is satisfiable exactly when the graph is 3-colorable.  If it is
not satisfiable, at least one of its finitely many edge constraints fails, so
its UNSAT value is at least `1/|E|`.

Apply [[dinur-constraint-gap-amplification]] repeatedly.  Perfect
satisfiability is preserved.  On a no-instance, the UNSAT value doubles until
it reaches the transformation's constant floor `alpha`; after
`O(log |E|)` iterations it is therefore bounded below by `alpha`.  Each round
has only constant-factor size growth and the number of rounds is logarithmic,
so the final constraint system still has polynomial size and constant alphabet
and arity.

A constant number of sequential repetitions raises the rejection probability
from `alpha` to at least `1/2`, increasing arity by only a constant.  This is
the gap-CSP form of the target.

Finally, use the elementary CSP/PCP correspondence.  The proof oracle is an
assignment to the constraint variables; the verifier uses `O(log n)` random
bits to choose a constraint uniformly and queries its `O(1)` entries.
Conversely, fixing a verifier's random string gives one constant-arity
constraint on the proof locations read under that string.  Rejection
probability is exactly the resulting constraint system's UNSAT value.  Thus
the gap-CSP statement yields the stated PCP theorem with perfect completeness
and soundness `1/2`.
