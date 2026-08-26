---
rg: 2
id: sl3-fold-square-from-two-mixed-a2-words
kind: route
title: Charge the swap fold square with the two symmetric mixed A2 words
target: sl3-swap-extension-has-defect-only-fold-square-rigidity
requires:
  - one-mixed-a2-word-does-not-control-fold-square
---

**INVALIDATED PROPOSAL.**  Enlarge the local torus/swap/rank-one interface by
both symmetric chamber identities

```text
W_12 E_23 W_12^*=[E_12,E_23],
W_23 E_12 W_23^*=[E_12,E_23]^(-1).                    (TMA1)
```

The second equality is the minimal chamber mate of the first: for the
standard simple Weyl words in `SL_3(Z)`, conjugation by `w_23` sends
`x_12(1)` to `x_13(-1)`, while
`[x_12(1),x_23(1)]=x_13(1)`.

`two-mixed-a2-words-do-not-control-fold-square` gives an exact dihedral
`M_2` packet satisfying `(TMA1)` and every earlier displayed input, but with
fold-Gram defect `3/32`.  Therefore these two mixed words still do not yield
a defect-only fold-square estimate.  A continuation must prevent the
root-collapse used by that packet, for example by consuming an additional
rank-one conjugacy relation or a closed chamber loop containing the opposite
root slots.

