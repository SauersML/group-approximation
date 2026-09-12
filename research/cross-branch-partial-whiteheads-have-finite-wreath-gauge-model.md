---
rg: 2
id: cross-branch-partial-whiteheads-have-finite-wreath-gauge-model
kind: claim
title: The two cross-branch partial Whiteheads retain a finite wreath-product gauge
artifacts:
  - research/cross-branch-partial-whitehead-wreath-proof.md
distinct_from:
  complementary-private-weyl-loops-have-s3-square-gauge-model: that keeps the two diagonal branch Weyl packets in direct-product factors; this adjoins the literal cross-branch partial equivalences and the actor which swaps those factors off-diagonally.
  binary-branch-flip-weyl-has-s3-c2-model: that gives a depth-one character/Pauli model for the aggregate branch flip; this computes the actual two partial opposite-root Whitehead factors and their action on the branch-resolved native `P_i,R_i,V_i` table.
  aggregate-binary-whitehead-does-not-read-completeness: that factorizes the aggregate row/column Whitehead branchwise without reverse products; this uses the cross matrix units `s_0t_1,s_1t_0` and obtains a genuine off-diagonal automorphism of the two branch S3 factors.
---

**ESTABLISHED CROSS-BRANCH GAUGE FENCE.**  Put

```text
p=s_0t_1,             r=s_1t_0,
pr=q_0,                rp=q_1,
p^2=r^2=0,             u=p+r,          u^2=1.         (CBW1)
```

On the native coordinate pair `(7,8)`, define the two actual partial
opposite-root Whiteheads

```text
K_0=x_78(p)x_87(r)x_78(p),
K_1=x_78(r)x_87(p)x_78(r).                             (CBW2)
```

Direct two-by-two block multiplication gives

```text
K_0^2=K_1^2=1,             [K_0,K_1]=1,
K_0K_1=w_78(u)=:T.                                     (CBW3)
```

Thus the two genuinely cross-branch private Whiteheads combine to the full
branch-flip Weyl; this factorization uses both partial equivalences, not only
the diagonal completeness signs.

Retain the branch-resolved native table

```text
P_i=x_78(q_i),        R_i=x_87(q_i),
V_i=P_iR_iP_i,
n=P_0P_1,             m=R_0R_1,       w=V_0V_1.       (CBW4)
```

The literal coefficient conjugations by `u` and the root-position swap in
`T` give the off-diagonal same-carrier rows

```text
TP_iT=R_(1-i),        TR_iT=P_(1-i),
TV_iT=V_(1-i),                                      (CBW5)

TnT=m,                TmT=n,             [T,w]=1.     (CBW6)
```

These relations really mix the two branch factors; they are stronger than
the diagonal direct-product table.  They still do not kill the native
order-three holonomy.

Let `B=S_3 times S_3`, with

```text
a=(1 2),              b=(2 3),              c=aba=(1 3).
```

Let `theta=Ad(c)` on `S_3` and let the involution `tau` act on `B` by

```text
phi(x,y)=(theta(y),theta(x)).                           (CBW7)
```

In the finite wreath-type group

```text
G=B semidirect_(phi) <tau>,                            (CBW8)
```

assign the two branch packets as

```text
P_0=(a,1), R_0=(b,1), V_0=(c,1),
P_1=(1,a), R_1=(1,b), V_1=(1,c),                     (CBW9)
```

and put

```text
n=(a,a),             m=(b,b),             w=(c,c),
T=tau.                                                     (CBW10)
```

Equations `(CBW5)--(CBW6)` hold exactly because `theta` swaps `a,b` and
fixes `c`.  Meanwhile

```text
wn=(ca,ca)                                              (CBW11)
```

has order three.  Hence the native Weyl gauge `D=w` and external-return
gauge `E=n` still neither commute nor cancel.

The factorization into the two private Whiteheads also has a finite gauge
realization.  In `G times C_2`, with central generator `z`, take

```text
k_0=z,                 k_1=z tau.                      (CBW12)
```

Then `k_0,k_1` are commuting nontrivial involutions and `k_0k_1=tau`,
exactly matching `(CBW3)`.  The individual partial Whiteheads do not
normalize the whole branch-resolved Hecke packet, so no additional
same-carrier conjugation equation for `k_0` or `k_1` is available before
their product `T` is formed.

This is an exact scoped model of the complete natural cross-branch table,
not a finite representation of the full EL20 presentation.  It shows that
the first genuine off-diagonal branch mixing only enlarges
`S_3 times S_3` to its finite branch-swap wreath extension; the diagonal
native `S_3` survives.  A positive ESB relation must compare one individual
partial Whitehead with a same-carrier native occurrence before the product
`K_0K_1=T`, rather than use only the aggregate flip rows `(CBW5)--(CBW6)`.

No Property T, Kazhdan input, local computation, trace hypothesis, or
literature theorem is used.

DERIVATION
cross-branch-partial-whitehead-wreath-proof
