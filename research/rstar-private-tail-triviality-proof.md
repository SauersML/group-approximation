---
rg: 2
id: rstar-private-tail-triviality-proof
kind: route
title: Extend shared bits independently through the two nonempty R-star fibres
target: rstar-private-tail-instances-are-trivial
requires: []
---

Choose arbitrary values for all shared variables.  Process each context
independently.  If it contains one shared variable, permute coordinates if
needed and use the corresponding nonempty coordinate fibre of `R_*`; if it
contains none, choose any allowed tuple.  Assign the selected tuple's other
coordinates to that context's private variables.  Since those variables
occur nowhere else, the choices glue to one global classical assignment.
