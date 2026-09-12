---
rg: 2
id: rstar-all-arity-polymorphism-proof
kind: route
title: Combine the arity-three census with Post's low-arity clone classification
target: rstar-polymorphism-clone-consists-only-of-projections
requires: []
---

The exhaustive standard-library computation checks all `4`, `16`, and `256`
truth tables in arities one, two, and three directly against all tuples from
`R_*`, leaving only the coordinate projections.

The polymorphisms of any relation contain all projections and are closed
under composition and identification of variables, hence form a Boolean
clone.  Post's classification says that a nonprojection Boolean clone has a
nonprojection member among its unary, binary, or ternary operations.  Applying
the contrapositive to the census proves the all-arities statement.

