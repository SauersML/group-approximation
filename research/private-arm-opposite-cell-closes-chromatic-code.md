---
rg: 2
id: private-arm-opposite-cell-closes-chromatic-code
kind: route
title: Put the private tagged column into the opposite-root Whitehead before multiplication
target: binary-leavitt-bounded-area-chromatic-code
requires:
  - marked-a3-output-whitehead-has-finite-gl4-model
---

**INVALIDATED PRIVATE-ARM OPPOSITE CELL.**  Put

```text
a=A_i+A_j,                 C=B_i+D_(ij)
```

and use the two shared-column opposite-root words

```text
P=x_14(a)x_41(C)x_14(a),
R=x_14(A_j)x_41(C)x_14(A_j).
```

The diagonal word contains the individual row and private tagged column
before `aC=q`; the edge word retains the same nonzero column and the
nonzero target arm `A_j`, so neither may be specialized to the identity at
the occurrence level.

`private-arm-opposite-cell-has-finite-m3-model` realizes this complete local
table over `M_3(F_2)`.  Both arms and the private tag are nonzero, the A3
marked/edge outputs and both opposite-root words are exact, yet the marked
root survives.  The two Whiteheads generate only a finite `S_3` absorber in
the model.  Hence sharing an individual private arm is still insufficient
without an additional full-Leavitt return relation that excludes this
finite coefficient specialization.

