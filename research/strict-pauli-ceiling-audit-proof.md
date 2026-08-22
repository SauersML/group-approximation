---
rg: 2
id: strict-pauli-ceiling-audit-proof
kind: route
title: Check the one-over-eighty-four margin and the strict ceiling overflow
target: strict-pauli-ceiling-audits-final-activator
requires:
  - marked-clifford-table-exponential-dimension
  - instance-modulated-kleene-microstate-diagonal
  - post-candidate-nemesis-has-a-finality-dilemma
---

Let `Def_(P_e)(U)<delta_e`.  The strict inequality in the microstate search
and `(SPC1)--(SPC2)` give

```text
eta < 1/84,
42 eta < 1/2.                                            (SPC3)
```

If `M_(w_e)(U)>1/2`, then `f(J)=w_e(U)` satisfies the marked hypothesis of
the Clifford-table theorem.  Hence

```text
D >= (1-4 eta^2) 2^N.                                   (SPC4)
```

But `(SPC3)` gives the **strict** estimate

```text
1-4 eta^2 > 1-4/84^2 = 1763/1764,                       (SPC5)
```

while the ceiling definition gives

```text
2^N >= (1764/1763)D.                                    (SPC6)
```

Combining `(SPC4)--(SPC6)` yields `D>D`, a contradiction.  Thus every
`D`-dimensional tuple of defect strictly below `delta_e` has
`M_(w_e)(U)<=1/2`, which is the required halting soundness.

Both small details are load-bearing.  Replacing `Def<delta_e` by
`Def<=delta_e` permits equality throughout `(SPC5)--(SPC6)` and gives only
`D>=D`.  Also the correct rank parameter here is the number `N` of Pauli
pairs in `E_N`, whose spin representation has dimension `2^N`; no extra
factor of two or floor from the alternative `n`-generator Clifford notation
should be inserted.

There is no recursive circularity in the conditional theorem.  The total
compiler computes `P_e,w_e,C_e` from the source index, and Kleene's recursion
theorem then supplies the fixed-point index.  The search can compute
`delta_e` before executing itself.  What would be circular is allowing
`C_e`, the presentation, or its relators to be chosen from the eventual halt
runtime or reported dimension.

