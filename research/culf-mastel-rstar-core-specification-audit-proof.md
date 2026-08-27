---
rg: 2
id: culf-mastel-rstar-core-specification-audit-proof
kind: route
title: Compare the NP-completeness invocation with the incidence data needed for peeling
target: culf-mastel-rstar-two-tail-core-is-not-specified
requires:
  - culf-mastel-rstar-reduction-is-support-blind
  - nonaffine-source-gadgets-force-a-pinned-two-tail-kernel
---

Corollary 6.7 records only the visible sets `V_i`, enlarged gadget variable
sets `W_i`, their intersections across different source contexts, and the
existential projection of `D_i` onto `C_i`.  Theorem 6.8 then obtains each
`D_i` by invoking NP-completeness and calls it the Boolean form of a whole
`CSP(Gamma)` instance.  Neither statement names that instance's atomic rows
or internal incidences.  The first prerequisite already audits this exact
gap in the claimed support argument.

A repository search finds theorem-level Cairn nodes and finite Fano-geometry
experiments but no implementation or serialized data choosing those pp
instances for the machine-indexed family.  Thus the row-variable incidence
input to two-tail peeling is absent both from the theorem and from the local
implementation.

Finally, the second prerequisite proves this missing choice cannot always be
made with empty pinned kernel: every gadget defining a nonaffine source
relation has a surviving dense row.  Supplying an explicit reduction would
therefore expose a real finite compatibility problem rather than make it
disappear automatically.

