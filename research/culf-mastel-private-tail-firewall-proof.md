---
rg: 2
id: culf-mastel-private-tail-firewall-proof
kind: route
title: Contrast row-private satisfiability with the published nonhalting gap
target: culf-mastel-rstar-has-no-private-tail-form
requires:
  - rstar-private-tail-instances-are-trivial
  - culf-mastel-rstar-fixed-language-gap-is-published
---

If every target occurrence in every member of the fixed family had at most
one nonprivate coordinate, the first prerequisite would give a classical
perfect assignment to every member.  A classical assignment is a
finite-dimensional CE strategy of value one.  This contradicts the second
prerequisite on any nonhalting input, where the family has a constant gap
from one.  Hence the proposed occurrence-private-tail normal form is not the
published fixed hard family.

Corollary 6.7 does not create a contradiction: `(PTA1)` separates auxiliary
sets belonging to different source contexts, not variables belonging to
different `R_*` rows inside one pp gadget.  Theorem 6.8 explicitly describes
each `D_i` as the Boolean form of a `CSP(Gamma)` instance before subdivision,
which is exactly the level at which internal auxiliary reuse remains.
