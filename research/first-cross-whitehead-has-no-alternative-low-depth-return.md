---
rg: 2
id: first-cross-whitehead-has-no-alternative-low-depth-return
kind: claim
title: The first cross Whitehead has no alternative one-root or same-pair Whitehead return
artifacts:
  - research/first-cross-whitehead-return-equation-proof.md
distinct_from:
  individual-cross-whiteheads-miss-native-hecke-target: that proves `K_0` itself misses the constant and native row-one targets; this solves the return equation after `K_0` for one arbitrary elementary root and for an arbitrary same-coordinate partial Whitehead.
  dyadic-cross-whitehead-fusion-has-finite-product-gauge: that factors `K_0` into its suffix-private pieces; this permits an arbitrary depth-changing partial inverse pair in a prospective second Whitehead.
  paired-critical-opposite-roots-return-only-trivially: that tests two opposite elementary roots in a critical root channel; this starts with the full three-root cross Whitehead and classifies a second Whitehead on its coordinate pair.
---

**ESTABLISHED LOW-DEPTH RETURN FENCE.**  Put

```text
K=K_0=[[q_1,p],[r,q_0]],       p=s_0t_1, r=s_1t_0,    (CRQ1)
```

on coordinates `(7,8)`.  There are two natural ways to try to erase the
nonconstant cut after `K`: append one elementary root in any actor channel,
or append another depth-changing partial Whitehead on `(7,8)`.  Neither
gives an independent return.

First use the literal `h=x_28(1)` in `L_0`.  As before,

```text
KhK=I+rE_27+q_0E_28=:I+e_2v.                         (CRQ2)
```

For an arbitrary elementary root `A=I+cE_ab`,

```text
A(KhK)A^(-1)=I+(Ae_2)(vA^(-1)).                      (CRQ3)
```

If the root does not meet row `2` or columns `7,8`, `(CRQ2)` is unchanged.
If it meets only one of those positions, the other one of the two entries
`r,q_0` is unchanged.  For a root within `(7,8)`, one of those two entries
is again unchanged, and for `b=2` both original row-two entries remain.
Thus at least one nonconstant entry survives in every case.  Consequently

```text
AK notin Norm(L_0,lambda_0)                           (CRQ4)
```

for every single elementary root `A`, with arbitrary Leavitt coefficient.

Now allow a full second partial Whitehead

```text
L=W_78(a,b)=x_78(a)x_87(b)x_78(a),
ab=e, ba=f, aba=a, bab=b.                             (CRQ5)
```

Its block is `[[1+e,a],[b,1+f]]`.  If `LK` returns to the signed normalizer,
then it is supported only on `(7,8)`.  Conjugating the two literal `L_0`
roots `x_79(1)` and `x_86(1)` shows first that every entry of such a
normalizing block lies in the embedded `F_2`.  The intersection of the
signed normalizer with this supported `GL_2(F_2)` block is exactly

```text
{1,x_78(1)}.                                          (CRQ6)
```

For return `LK=1`, uniqueness gives `L=K`; this is the old involution
relation and has no independent occurrence gauge.  For `LK=x_78(1)`, the
forced block `L=x_78(1)K` has

```text
L_12=p+q_0,       L_21=r,       L_11=q_1+r.           (CRQ7)
```

But a Whitehead with those off-diagonal entries would require

```text
L_11=1+(p+q_0)r=1+q_0=q_1,                            (CRQ8)
```

contradicting `(CRQ7)`.

The native target is equally rigid.  Since `J_1,L,K` are supported on the
same pair, `LK in J_1 Norm(L_0,lambda_0)` again permits only the two
relative constants in `(CRQ6)`.  For `N=1` or `x_78(1)`, the forced block

```text
L=J_1 N K                                             (CRQ9)
```

has the same off-diagonal entries

```text
L_12=y_1=s_0t_00,          L_21=r.                    (CRQ10)
```

Their product is zero, so a Whitehead block requires `L_11=1`.  The actual
upper-left entries are respectively

```text
q_1,                     q_1+r,                       (CRQ11)
```

and neither is one.  Hence no depth-changing same-pair Whitehead takes the
`K_0` cut to `J_1QJ_1^(-1)`.  Because `t_1=J_1v_1` with `v_1` in the signed
normalizer, the same conclusion holds for the Singer target.

The coarse `K_1` equation has the same uniqueness obstruction for returns
to `Q`, by swapping the two coordinate directions.  Thus the natural
second-object erasers at this depth consist only of the literal inverse
`K_i` itself.  Its gauge relation is merely `k_i^2=1`; it cannot authenticate
or cancel an independent native reservoir factor.

This fence does not classify a product of two additional nonnormal words in
two different root channels.  Such a word must use both occurrences
essentially: neither one may be an elementary return, and their product
must escape the same-pair block equations `(CRQ7)--(CRQ11)`.

No Property T, Kazhdan input, trace hypothesis, literature theorem, local
computation, or Lean compilation is used.

DERIVATION
first-cross-whitehead-return-equation-proof
