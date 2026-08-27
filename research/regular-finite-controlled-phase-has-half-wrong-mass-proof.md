---
rg: 2
id: regular-finite-controlled-phase-has-half-wrong-mass-proof
kind: route
title: Decompose the finite regular representation into cosets of the selector-phase subgroup
target: regular-finite-controlled-phase-has-half-wrong-mass
requires: []
---

Choose left-coset representatives for `C` in `H`.  Each coset span is
invariant under left multiplication by `C` and, after translation by its
representative, is exactly the regular `C`-module.  Hence

```text
lambda_H restricted to C = lambda_C^([H:C]).                    (RCP2)
```

Every character of the finite abelian group `C` occurs once in `lambda_C`,
so all joint characters have the same multiplicity in `(RCP2)`.

If `c in D`, evaluation of `c` is a character monomial in the Boolean
generators and is affine in their exponent bits.  If `c notin D`, then
`C=D direct-sum <c>` because `c` is an involution.  Every `x in D^` therefore
has precisely two extensions to `C`, differing only in the sign assigned to
`c`; `(RCP2)` gives them equal multiplicity and proves `(RCP1)`.

