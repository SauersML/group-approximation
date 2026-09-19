---
rg: 2
id: bcs-compressed-cuntz-coupling-audit-proof
kind: route
title: Compare the two independent finite lower bounds and localize the only useful upper bound
target: bcs-to-compressed-cuntz-coupling-is-not-a-smaller-gate
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - orthogonal-compressed-word-branches-have-cuntz-rank-floor
  - central-sign-bcs-energy-decoder-implies-nonhyperlinear
---

Normalize the robust BCS inequality on the marked corner.  Multiplying its
normalized corner trace by the ambient corner mass gives

```text
B>=beta_B q.                                           (BCP1)
```

The compressed Cuntz rank inequality gives independently

```text
D>=(k-1)q.                                             (BCP2)
```

An upper comparison `D<=CB` combines `(BCP2)` with `B` only in the direction
`B>=(k-1)q/C`, so it cannot make any presentation defect positive.  If an
upper bound by `delta` is supplied for `B` or `D`, `(BCP1)` or `(BCP2)` alone
already gives the terminal marked payment.  This proves the first two cases.

For the localized case, `(BCC6)` and `D<=AW` give

```text
aL<=AW,
```

which is CPS12.  Conversely, if `L<=KW`, then the upper half of `(BCC6)`
gives `D<=(bK+O(1))W`.  Hence the two formulations differ only by fixed
constants.

Finally, if the bound `D<=A delta` is valid in every finite tracial
representation of the fixed group-algebra identities, substitute the left
regular representation with `delta=0`.  The Cuntz floor forces the faithful
trace of the marked projection to vanish.  The same proof works in a finite
von Neumann algebra: the right support of `Q_iU_iE` is Murray--von Neumann
subequivalent to `Q_i`, so its kernel inside `E` has trace at least
`tau(E)-tau(Q_i)`.  Thus an all-tracial formulation
collapses the mark, while a finite-matrix-only formulation is exactly the
unresolved decoder rather than a formal consequence of the BCS lower bound.
