---
rg: 2
id: deligne-sep8-first-order-tensor-threshold-proof
kind: route
title: Amplify a vanishing parameter by a reciprocal number of tensor factors
target: deligne-sep8-first-order-tensor-threshold
requires:
  - deligne-sep7-all-cover-mf-radical-classification
artifacts:
  - research/artifacts/deligne-sep8-first-order-tensor-threshold.md
---

The prerequisite gives `1 iff 2`. If `P_op=R/Z`, choose `t_n=1/n`
for `n>=2` and a single `t_n` model with error below `t_n^2` on the first
`n` multiplication pairs. This yields assertion 3.

For `3 implies 2`, conjugate the matrices whenever `t_n<0`, so that the
parameters are positive. Fix any real representative `theta in [0,1)`.
For `theta>0`, set `k_n=floor(theta/t_n)` after discarding the finite
initial segment on which this is zero, and put
`V_n(g)=U_n(g)^(tensor k_n)`. Tensor telescoping bounds the defect at each
fixed pair by `k_n o(t_n)=o(1)`, and the multiplier is
`exp(2 pi i k_n t_n b(g,h))`. Since `k_n t_n->theta`, these are
point-norm models at `theta`. The parameter zero has the trivial model.
Thus every parameter belongs to `P_op`.

For the quantitative assertion, tensoring tuples, conjugating tuples, and
comparing phases give, respectively,

```text
f_W(x+y)<=f_W(x)+f_W(y),
f_W(-x)=f_W(x),
|f_W(x)-f_W(y)|<=L dist(x,y).
```

The tensor inequality for infima follows by taking tuples arbitrarily
close to both infima and then letting the two approximation errors tend
to zero. No dimension bound or attained infimum is needed.

The hypothesis forces `L>0`, because when `b` vanishes on `W` the identity
tuple has zero defect at every parameter. For `0<t<=a` take
`k=floor(a/t)>=1`. Then `0<=a-kt<t` and therefore

```text
k f_W(t) >= f_W(kt) >= epsilon-Lt.
```

If in addition `t<=epsilon/(2L)`, the right side is at least
`epsilon/2`. Since `k<=a/t`, this proves
`f_W(t)>=epsilon t/(2a)`. Conjugation handles negative `t`.
The artifact audits the quantifiers and identifies the open input.
