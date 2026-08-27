---
rg: 2
id: b2-b3-full-hecke-four-sector-proof
kind: route
title: Pair the r sign inside each t sector and then balance the two t marginals
target: b2-b3-pair-full-hecke-four-native-sectors
requires:
  - b2-pairs-full-hecke-first-support
  - center-chain-mixed-hecke-overlap-is-common-pauli-source
  - native-whitehead-corner-collapses-hecke-flags
---

The proof of `b2-pairs-full-hecke-first-support` checks that `r` and `B_2`
normalize `(L_0,lambda_0)` and that `B_2` flips the `r` sign on `Q`.
We verify the second pair directly.

Recall

```text
H=<x_65(q),x_54(q),x_42(q)>,
t=x_69(a_3),                   B_3=x_95(b_3).          (1)
```

Conjugation by `t` fixes the generators of `L_0` except for

```text
f=x_94(b_3)       |-> f x_64(q),
k=x_92(b_3)       |-> k x_62(q),
c=x_97(b_3a_1)    |-> c w,                            (2)
```

up to orientation.  The first two corrections are positive derived roots
of `H`, and `w=x_67(a_1)` also has positive `lambda_0` sign.  Here we used
`a_3b_3=q` and `a_3b_3a_1=qa_1=a_1`.  Hence `t` normalizes the signed pair.

Conjugation by `B_3` fixes the generators of `L_0` except for the positive
corrections

```text
x_54(q) |-> x_54(q)f,
x_52(q) |-> x_52(q)k,
v=x_57(a_1) |-> vc,                                  (3)
```

again up to orientation.  These are elements already carrying positive
`lambda_0` sign.  Thus `B_3` also normalizes `(L_0,lambda_0)`.

The adjacent-root row gives

```text
[t,B_3]=x_65(a_3b_3)=x_65(q)=C_3.                    (4)
```

Since `C_3Q=-Q`, equation `(4)` says

```text
(B_3Q)(tQ)(B_3Q)^*=-tQ.                              (5)
```

Thus the positive and negative `t` eigenspaces in `QH` have equal rank.

Now `r` and `t` commute, so the four operators in `(BQS3)` are orthogonal
projections summing to `Q`.  Moreover `[B_2,t]=1`.  The `B_2` flip from
`b2-pairs-full-hecke-first-support` therefore gives, separately for each
fixed `delta`,

```text
rank(E_(+,delta))=rank(E_(-,delta)).                  (6)
```

Write these common values as `m_+` for `delta=+` and `m_-` for
`delta=-`.  Equation `(5)` equates the total two `t` marginals, hence

```text
2m_+=rank(Q(1+t)/2)=rank(Q(1-t)/2)=2m_-.             (7)
```

All four joint ranks are therefore equal.  Since they sum to `rank(Q)`,
each is `rank(Q)/4`, proving `(BQS4)`.

Finally `native-whitehead-corner-collapses-hecke-flags` computes on the
coarser source `p_2`

```text
p_2(J_1p_2J_1)p_2=p_2(1+r)/2,
p_2(J_2p_2J_2)p_2=p_2(1+t)/2.                        (8)
```

Since `Q<=p_2` and both `r,t` reduce `Q`, compressing `(8)` by `Q` gives
`(BQS5)`.  The two commuting source supports meet in `(BQS6)`, whose rank
is `(BQS4)` with signs `(+,+)`.
