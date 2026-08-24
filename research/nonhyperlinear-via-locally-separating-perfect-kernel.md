---
rg: 2
id: nonhyperlinear-via-locally-separating-perfect-kernel
kind: route
title: Quotient a perfect non-CE contextual model by its locally separating group kernel
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - non-ce-bcs-has-locally-separating-perfect-kernel
  - forbidden-character-kernel-quotient-compiler
---

Take the contextual group skeleton and perfect tracial representation from
`non-ce-bcs-has-locally-separating-perfect-kernel`.  Choose one kernel
witness detected by each forbidden character and quotient by the normal
closure of those finitely many witnesses.  The central sign survives, while
every forbidden context character idempotent vanishes by `(FKQ5)`.  A
hypothetical hyperlinear embedding of the quotient would yield, in its
central `J=-1` corner, a Connes-embeddable perfect trace for the original
BCS.  This contradicts `mipstar-bcs-tracial-nonru-exists`.
