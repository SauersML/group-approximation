---
rg: 2
id: polar-covariance-transfer-proof
kind: route
title: Commute the inverse square root through the compressed observable
target: polar-correction-preserves-povm-covariance
requires:
  - common-source-partial-isometries-decode-one-game-state
---

Put `R=(AY-YB)P`.  Then `||R||_2<=epsilon` and, because `Y=YP`,

```text
R=AY-YB_P.                                              (PCP1)
```

Since `A=A^*`,

```text
[B_P,H]=Y^*R-R^*Y,
||[B_P,H]||_2<=2epsilon.                               (PCP2)
```

The integral formula

```text
H^(-1/2)=(1/pi) int_0^infinity
 t^(-1/2)(H+tP)^(-1) dt                               (PCP3)
```

and the resolvent commutator identity give

```text
||[B_P,H^(-1/2)]||_2
 <=(1/2)lambda^(-3/2)||[B_P,H]||_2
 <=lambda^(-3/2)epsilon.                              (PCP4)
```

Finally,

```text
AS-SB_P
 =R H^(-1/2)+Y[B_P,H^(-1/2)].                         (PCP5)
```

Use `||H^(-1/2)||<=lambda^(-1/2)` and `||Y||<=1` to
obtain `(PCV4)`.

For the off-source part,

```text
(AY-YB)(1-P)=-YPB(1-P).
```

The lower bound `Y^*Y>=lambda P` therefore gives

```text
||PB(1-P)||_2<=lambda^(-1/2)epsilon.                   (PCP6)
```

Since `S` is isometric on `P`, combine `(PCV4)` with

```text
AS-SB=(AS-SB_P)-SPB(1-P)
```

to obtain `(PCV5)`.
