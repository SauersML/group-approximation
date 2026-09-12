---
rg: 2
id: leavitt-24k-kernel-packet-excludes-scalar-field-models
kind: claim
title: Four explicit 24k kernel words reject the displayed F8 model and every literal scalar-field elementary assignment
distinct_from:
  leavitt-24k-first-relation-has-exact-finite-model: that exhibits an exact F8 solution of the first relation; this gives three further native kernel words, two of which have defect exactly square root two in that model.
  leavitt-24k-feasibility-has-a-uniform-gap: that asks for one dimension-uniform lower bound over all relative unitaries; this supplies an explicit finite test packet and excludes only the stated elementary model class.
artifacts:
  - research/artifacts/leavitt-24k-finite-coefficient-kernel-packet-2026-09-08.md
---

Use the map `q:P=C_3*C_2^3 -> EL_3(L_(F_2)(1,2))` with
`c=(123)` and `b_1=x_12(s)`, `b_2=x_12(t)`, `b_3=x_12(v)`, where
`s=s_0`, `t=t_0`, and `v=s_0t_1+s_1t_0`. Define straight-line words

```text
gamma(W)=c W c^(-1),
d=[b_2,gamma(b_1)],       h=gamma^2(d),
a=[d,h],                 e=gamma(d),
j=a e a^(-1),
u=[b_2,gamma(b_3)],       w=[gamma^2(b_1),a].
```

Then the following four words lie in `ker q`:

```text
r_* = j c j c,
R_v = [b_3,gamma(b_3)] d^(-1),
R_0 = [u,w],
R_sum = [[b_1,gamma(b_2)],h]
        [[b_3,gamma(b_1)],gamma^2(u)] a^(-1).
```

Their unexpanded word-length bounds in the letters
`c,c^(-1),b_1,b_2,b_3` are respectively `166,16,172,108`.

In the displayed `GL_3(F_8)` assignment
`(b_1,b_2,b_3)=(x_12(alpha),x_12(alpha^(-1)),x_12(1))`,
the first two words are the identity and the last two are `x_12(1)`.
Thus `R_0` and `R_sum` each have normalized-HS defect exactly `sqrt(2)`
in its left regular representation, including after conversion to the
frozen `24k` coordinates.

More generally, `R_0` is nonidentity in every assignment over a field
of characteristic two with the same coordinate cycle and all three
`b_i=x_12(s),x_12(t),x_12(v)` nonidentity. Before any coefficient
normalization, its coefficient is `t v s (ts)^2`, which is nonzero
in a field under those assumptions.

This finite packet is not asserted to present the Leavitt unit group.
The scalar-field argument alone does not exclude
arbitrary finite-group models, arbitrary block-matrix coefficient models,
or all relative unitaries in the 24k problem. No dimension-uniform
normalized-HS gap is proved.

The abstract finite-model question for this packet is now settled by
`leavitt-four-word-packet-has-an-exact-24-dimensional-model`: all four
words vanish in an explicit frozen permutation model of dimension 24,
whose image is `S_3 x C_2^2`. Its derived word `d` has order three
instead of the native order two. The separate finite-coefficient
rank-gap theorem remains valid for its stated realization class.
