---
rg: 2
id: hyperlinear-implies-sofic-via-bounded-width-compiler
kind: route
title: Compile the regular-character loss to bounded width and invoke the operator no-gap theorem
target: hyperlinear-implies-sofic
requires:
  - bounded-width-regular-character-compiler
  - bounded-width-operator-csp-no-gap
---

Fix a finite group window and an error target. Hyperlinearity makes the
corresponding regular-character unitary loss arbitrarily small. By
`bounded-width-regular-character-compiler`, this produces an operator solution
of a bounded-width finite-domain instance. `bounded-width-operator-csp-no-gap`
removes the operator/classical satisfiability gap, and the compiler's decoding
clause turns the resulting classical assignment back into a finite action with
small original loss. Running this on arbitrary windows yields soficity.
