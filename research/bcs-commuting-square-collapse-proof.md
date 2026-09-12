---
rg: 2
id: bcs-commuting-square-collapse-proof
kind: route
title: Expand the transported commutator and audit the two BCS input rows
target: bcs-commuting-square-transfer-collapses-britton-commutator
requires:
  - deleting-one-gap-row-has-the-wrong-orientation
  - context-local-fanizza-exits-do-not-control-global-leakage
  - perfect-tracial-bcs-has-one-common-module-swap
  - twisted-disagreement-return-factors-through-localized-commutator
---

Conjugating the private context relation gives

```text
[c,c_0]=t^(-1)[a,a_0]t.
```

If `c_0=b_0`, this is exactly `(BCS2)`.  Thus an ordinary presentation
containing the two familiar BCS rows makes the proposed terminal word a
relator consequence.

For matrices, write `E=B_0-C_0`.  The additive commutator identity

```text
[C,B_0]=[C,C_0]+CE-EC
```

and unitary invariance give

```text
||[C,B_0]||_2
 <=||[C,C_0]||_2+2||E||_2
 = ||[A,A_0]||_2+2||C_0-B_0||_2,
```

which proves `(BCS3)`.  If `Q` commutes with `C`, left multiplication by
`Q` in the same identity gives

```text
QCE=CQE,                 QEC=QEC.
```

Both error terms have norm at most `||QE||_2`, proving `(BCS4)`.

The cited deleted-row theorem rules out reversing the finite-game lower
bound into the missing upper bound.  The cited Bass--Serre countermodel
rules out deriving the mixed commutator from context-local packet rows.  The
standard-form theorem supplies exact infinite completeness but records the
same unexposed common-swap gate.  Finally, the twisted-disagreement theorem
shows that positive-density localized cross-commutation itself is already a
complete return carrier, so no additional disagreement construction remains
after `(BCS4)`.

