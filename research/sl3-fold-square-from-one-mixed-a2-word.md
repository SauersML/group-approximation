---
rg: 2
id: sl3-fold-square-from-one-mixed-a2-word
kind: route
title: Charge the swap fold square with the first mixed A2 word
target: sl3-swap-extension-has-defect-only-fold-square-rigidity
requires:
  - unbalanced-torus-and-swap-commutation-do-not-control-fold-square
---

**INVALIDATED PROPOSAL.**  Add the first mixed rank-two identity

```text
W_12 E_23 W_12^*=[E_12,E_23]
```

to the exact local interface consisting of the two unbalanced torus closures,
the swap commutators, and the separate root-doubling/Weyl-word identities.
Attempt to bound the fold-square defect using only the defects of this enlarged
finite package.

`one-mixed-a2-word-does-not-control-fold-square` gives an exact `M_4`
countermodel: every input equality, including the mixed word, holds exactly,
but the normalized squared fold defect is `3` and the fold-Gram defect is
`3/32`.  Thus no dimension-free estimate using only this package can prove the
target, regardless of constants.

The countermodel is not an assignment of the full `SL_3(Z)` presentation.  A
positive continuation must use more joint rank-two coherence than this single
eliminated-root identity, such as a second competing chamber return or a
closed `A_2` loop which prevents the internal repair unitary used by the
countermodel.

