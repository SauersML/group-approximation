---
rg: 2
id: odd-nand-cycle-cancels-separators-to-central-phase-proof
kind: route
title: Order the local signed words so every repeated cycle variable cancels adjacently
target: odd-nand-cycle-cancels-separators-to-central-phase
requires:
  - nand-sheet-swap-cannot-be-a-pure-central-phase
---

Substitute `(ONC1)` into `(ONC2)` and use centrality of `J`:

```text
W_C=J^n (X_1X_2)(X_2X_3)...(X_(n-1)X_n)(X_nX_1).       (ONP1)
```

The two copies of `X_2` are adjacent, so they cancel by involutivity.  The
resulting copies of `X_3` are then adjacent and cancel, and so on.  After the
`X_n` cancellation, `(ONP1)` ends with `X_1X_1=q`.  Thus the entire variable
word is `q`, proving `(ONC3)`.  This argument never interchanges two factors;
in particular it does not assume that variables in nonadjacent contexts
commute.

If `n` is odd, central involutivity gives `J^n=J`, proving `(ONC4)`.  If `n`
is even, the same calculation gives the sharp complementary result `W_C=q`.
