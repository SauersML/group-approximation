---
rg: 2
id: p13-rotation-relator-defect-219-proof
kind: route
title: Expand every derived replay consequence and telescope
target: p13-rotation-relator-defect-219
requires: []
artifacts:
  - GroupApproximation/Sofic/LiteralBaseP13RotationReplay.lean
  - GroupApproximation/Sofic/LiteralBaseP13RotationQuotient.lean
---

## Direct proof

Each call of `LiteralBaseP13RotationReplay.rotationStep` certifies in the free
group that

```text
current*next^{-1}=a*r^{+/-1}*a^{-1}
```

for one of the eight defining rotation relators `r`. Evaluation on unitaries
and unitary invariance of operator norm therefore give

```text
||current(X,Y,Z)-next(X,Y,Z)|| <= delta.
```

Triangle inequality along a trace charges one `delta` per primitive step.
A `rotationConsequenceStep` must instead be charged the fully expanded cost
of the previously proved consequence that it inserts. Expanding that acyclic
dependency graph gives:

| P13 relator | primitive steps | inserted consequences | total cost |
|---|---:|---|---:|
| `S123` | 59 | none | 59 |
| `S132` | 24 | `O12_32`, `O12_13`, `O21_23` | 122 |
| `S213` | 20 | `O13_23`, `O21_23`, `O12_13` | 116 |
| `S231` | 9 | `S123` | 68 |
| `S312` | 59 | none | 59 |
| `S321` | 60 | none | 60 |
| `O12_13` | 4 | `O31_32` | 43 |
| `O12_32` | 18 | none | 18 |
| `O13_23` | 16 | none | 16 |
| `O21_23` | 37 | none | 37 |
| `O21_31` | 37 | none | 37 |
| `O31_32` | 39 | none | 39 |
| `Torsion` | 72 | `O12_32` once, `O12_13` three times | 219 |

The nontrivial arithmetic is

```text
O12_13 = 4+39 = 43,
S132    = 24+18+43+37 = 122,
S213    = 20+16+37+43 = 116,
S231    = 9+59 = 68,
Torsion = 72+18+3*43 = 219.
```

Thus the largest fully expanded area is `219`, proving the uniform bound.
The surjectivity witness traces are not P13 relators; their expanded costs are
`17` for `RangeXY` and `34+37=71` for `RangeZ`.
