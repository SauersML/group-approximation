---
rg: 2
id: marked-output-whitehead-closes-a3-chromatic-cell
kind: route
title: Attach one opposite-root Whitehead directly to the tagged A3 marked output
target: binary-leavitt-bounded-area-chromatic-code
requires:
  - tagged-a3-associator-cell-has-finite-positive-root-model
---

**INVALIDATED OUTPUT-WHITEHEAD ROUTE.**  Complete the direct tagged
associator by adjoining the opposite long root `x_41(q)` and the partial
Whitehead

```text
W_q=x_14(q)x_41(q)x_14(q).
```

This is the shortest opposite-root occurrence literally containing the
payload-produced marked output `x_14(q)`.  Its conjugacy row leaves the
positive radical and cannot be covered by positive-root local finiteness.

`marked-a3-output-whitehead-has-finite-gl4-model` nevertheless gives an
exact finite marked specialization in `GL_4(F_2)`.  The associator, edge-zero
row, opposite root, Whitehead factorization, and output conjugacy all hold,
while the marked transvection remains nontrivial.  Attaching the opposite
root only after the private coefficients have multiplied to `q` erases the
address payload and does not yield a chromatic decoder.

