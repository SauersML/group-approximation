---
rg: 2
id: bounded-area-conjugacy-difference-code-proof
kind: route
title: Color vertex evaluations by a finite operator-norm net
target: bounded-area-conjugacy-difference-code-kills-mf-mark
requires:
  - bounded-relator-area-controls-opnorm-word-defect
---

Let `U_n` be presentation models with `Def_R(U_n)=delta_n->0`.  Fix
`epsilon>0` and one coordinate `n`.  Compactness of `U(d_n)` supplies a
finite cover by sets of operator-norm diameter at most `epsilon`.  Color
`v in V` by a cover element containing `b_v(U_n)`.  Since `Lambda` has
infinite chromatic number, some edge `vw` is monochromatic, and hence

```text
||b_v(U_n)^(-1)b_w(U_n)-I||_op<=epsilon.                (CDP1)
```

The bounded-area estimate `(CDC2)` and
`bounded-relator-area-controls-opnorm-word-defect` give

```text
||b_v(U_n)^(-1)b_w(U_n)
   -a_(v,w)(U_n)z(U_n)a_(v,w)(U_n)^(-1)||_op
 <= A delta_n.                                         (CDP2)
```

Unitary invariance and `(CDP1)--(CDP2)` imply

```text
||z(U_n)-I||_op<=epsilon+A delta_n.                     (CDP3)
```

The selected edge may depend on `n`; uniformity of `A` is exactly what makes
that harmless.  First let `n` tend to infinity and then let `epsilon` tend to
zero.  Every norm-corona representation kills `z`, proving `(CDC3)`.
