---
rg: 2
id: chromatic-mark-codes-metric-agnostic-proof
kind: route
title: Rerun the finite-net coloring in any compact group with a bi-invariant metric
target: chromatic-mark-codes-are-metric-agnostic
requires: []
---

**Step 1: area controls defect in any bi-invariant metric.**  Suppose a
free word `w` equals, freely, `prod_(k=1)^A g_k r_k^(e_k) g_k^(-1)`.
Evaluate at `phi` in `G`.  Bi-invariance gives
`d(g r^(e) g^(-1),1)=d(r,1)`.  Using bi-invariance and the triangle
inequality, `d(xy,1)<=d(x,1)+d(y,1)`.  Free reduction does not change the
evaluation.  Hence

```text
d(w(phi),1) <= A delta(phi).                              (MP1)
```

This is `bounded-relator-area-controls-opnorm-word-defect` with the operator
norm replaced by `d`.  Its proof never used anything else.

**Step 2: conjugacy-difference codes.**  Fix `epsilon>0` and `n`.  Since
`G_n` is compact, finitely many `d_n`-balls of radius `epsilon/2` cover it.
Color each vertex `v` by a ball containing `b_v(phi_n)`.  Infinite chromatic
number gives an edge `vw` whose endpoints fall in the same ball, so
`d_n(b_v(phi_n),b_w(phi_n))<=epsilon`.  By bi-invariance this is
`d_n(b_v(phi_n)^(-1)b_w(phi_n),1)<=epsilon`.  By `(CDC2)` and `(MP1)`,

```text
d_n(b_v^(-1)b_w(phi_n), a z a^(-1)(phi_n)) <= A delta_n.
```

Conjugation invariance then gives
`d_n(z(phi_n),1)<=epsilon+A delta_n`.  The edge may depend on `n`; `A` does
not.  Let `n->infinity`, then `epsilon->0`.

**Step 3: commutator codes.**  In a bi-invariant metric,

```text
d([x,h],[y,h]) = d(x h x^(-1), y h y^(-1))
              <= d(x,y) + d(x^(-1),y^(-1)) = 2 d(x,y).    (MP2)
```

Color vertices by an `epsilon/2`-net for `c_v(phi_n)`.  A monochromatic
edge `vw` gives `d_n(c_v(phi_n),c_w(phi_n))<=epsilon`.  Write `X(phi_n)` as
`X` for short.  Conjugation invariance, `(CCC1)` and `(MP1)` give
`d_n(z,1)=d_n(a_v z a_v^(-1),1)<=A_Delta delta_n+d_n([c_v,h_v],1)`.  By
`(MP2)`, `d_n([c_v,h_v],[c_w,h_v])<=2 epsilon`.  By `(CCC2)` and `(MP1)`,
`d_n([c_w,h_v],1)<=A_0 delta_n`.  Hence

```text
d_n(z(phi_n),1) <= (A_Delta+A_0) delta_n + 2 epsilon.
```

This proves `(MA1)` in both cases.

**Step 4: hyperlinearity.**  If `Gamma` is finitely presented and hyperlinear
and `z!=1`, there are `phi_n:S->U(k_n)` with normalized-HS relator defects
tending to zero and `||z(phi_n)-I||_2 -> sqrt(2)`.  These are the
regular-character microstates.  This contradicts `(MA1)` for the
normalized-HS metric, which is bi-invariant because the normalized trace is
unitarily invariant.  So `z=1`, which is `(MA2)`.  Sofic groups are
hyperlinear.

**Step 5: Leavitt consequence.**  In the goal presentation,
`z=x_13(s_1t_1)!=1`: its elementary-matrix image has nonzero off-diagonal
coefficient.  So a code solving `binary-leavitt-bounded-area-chromatic-code`
makes `Delta` nonhyperlinear by `(MA2)`.  Simplicity is not needed.
