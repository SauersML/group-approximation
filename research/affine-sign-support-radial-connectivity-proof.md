---
rg: 2
id: affine-sign-support-radial-connectivity-proof
kind: route
title: Turn each support component into a smaller simplex codeword
target: affine-sign-support-is-radially-connected
requires:
  - radial-only-group-needs-a-cyclic-gcd-audit
---

Within a four-local context all support vertices co-occur, so a context
cannot meet two different support components.  Its even intersection with
the original codeword is therefore an even intersection with each component
indicator.  Exactness of the classical kernel puts every component indicator
back in the punctured affine simplex code.  The three-weight calculation
`(ASC2)` excludes a proper split, except for the constant word, whose support
is connected by the radial `x--alpha x` cycle.
