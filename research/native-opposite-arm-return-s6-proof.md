---
rg: 2
id: native-opposite-arm-return-s6-proof
kind: route
title: Overlap the native fold and partial Whitehead inside S6
target: native-opposite-arm-return-has-finite-s6-model
requires:
  - leavitt-range-sum-fold-is-first-object-erasing-row
---

First, the root-index words are genuine null-relation consequences.  The
ordinary Steinberg formula gives

```text
[x_15(q_i),x_56(s_0)]=x_16(q_i s_0),
[x_01(t_0),x_16(s_0)]=x_06(t_0s_0).                   (1)
```

The Leavitt identities `q_0s_0=s_0`, `q_1s_0=0`, and `t_0s_0=A` prove
`(NOA2)`.  On the `(1,6)` block,

```text
R=[[1,s_0],[0,1]],              L=[[1,0],[t_0,1]],
P=RLR=[[1+s_0t_0,s_0],[t_0,0]].                        (2)
```

Using `t_0s_0=A`, `(1+s_0t_0)s_0=0`, and
`t_0(1+s_0t_0)=0`, another block multiplication proves `(NOA4)`.  Fixed
permutation matrices on spare Steinberg indices give `(NOA5)--(NOA6)`.

It remains to verify the finite model.  Every permutation in `(NOA7)` is
an involution except `V`, which has order four.  Cancellation of the common
factor `(4 5)` gives

```text
C_0C_1=(1 2)(3 6)=J.                                  (3)
```

Direct conjugation and multiplication give

```text
[C_0,S]=(3 6)(4 5)=R,       [C_1,S]=1,
[J,S]=R,                    [T,S]=1,
[T,R]=(3 4)(5 6)=Z.                                  (4)
```

The common transposition `(4 5)` in `R,L` cancels from their noncommuting
three-point part, where `(3 6)` and `(2 3)` are adjacent transpositions.
Hence

```text
RLR=LRL,                 P^2=1,
PRP^(-1)=L,              PLP^(-1)=R.                  (5)
```

Finally, conjugation simply transports the unordered transposition pairs:

```text
USU^(-1)=(3 6)(4 5)=R,
QLQ^(-1)=(1 2)(5 6)=T,
VJV^(-1)=(3 4)(5 6)=Z.                                (6)
```

Also `U^2=Q^2=1` and `V^4=1`.  This proves every displayed occurrence row.
The generated subgroup of `S_6` is finite and `Z` is a nonidentity
involution, so its left regular representation has zero cell defect and
`||lambda(Z)-1||_op=2`.

