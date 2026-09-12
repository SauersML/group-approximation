---
rg: 2
id: complementary-private-weyl-loops-have-s3-square-gauge-model
kind: claim
title: The literal complementary private-Weyl same-chart loops retain an S3 by S3 gauge
artifacts:
  - research/complementary-private-weyl-s3-square-proof.md
distinct_from:
  complementary-depth-two-a3-whiteheads-have-a6-gauge-model: that uses completeness, the aggregate Whitehead product, and chart conjugacy; this derives the actual same-chart commutator and conjugation loops between each private Whitehead and the native constant roots.
  native-weyl-return-gauges-have-s3-model: that treats only the aggregate constant roots `n,m,w`; this splits all three into their two complementary coefficient occurrences and retains every branchwise conjugation identity.
  reverse-product-whitehead-fold-has-finite-fusion: that proves `V_0V_1=w`; this adds the branchwise relations `nV_in=R_i`, `mV_im=P_i`, and `[w,V_i]=1` and gives their complete finite gauge table.
---

**ESTABLISHED SAME-CHART LOOP FENCE.**  Let

```text
q_i=s_it_i,                 q_0+q_1=1,
P_i=x_78(q_i),              R_i=x_87(q_i),
V_i=P_iR_iP_i.                                        (CPW1)
```

The depth-two A3 cells of
`complementary-depth-two-a3-whiteheads-have-a6-gauge-model` authenticate the
two `P_i` before the opposite-root words `V_i` are formed.  Put

```text
n=x_78(1)=P_0P_1,
m=x_87(1)=R_0R_1,
w=nmn=V_0V_1.                                         (CPW2)
```

Because `q_0q_1=q_1q_0=0`, all branch-zero root operators commute with all
branch-one root operators, including the opposite-root pairs.  The ordinary
two-by-two Whitehead identities on each branch therefore give the literal
same-chart EL20 loops

```text
nV_in=R_i,
mV_im=P_i,
wV_iw=V_i,                 i=0,1.                     (CPW3)
```

In particular `(CPW3)` contains the hoped-for nontrivial commutator

```text
[w,V_i]=1.                                             (CPW4)
```

It is genuinely stronger than the product relation `V_0V_1=w`: it couples
each individual complementary private Whitehead to the native constant
Weyl occurrence on one carrier.

The new loop still does not force the native Whitehead and external-return
gauges to commute.  The entire branch-resolved gauge table has the following
exact finite solution in `S_3 times S_3`.  With

```text
a=(1 2),              b=(2 3),              c=aba=(1 3),
```

put

```text
P_0=(a,1), R_0=(b,1), V_0=(c,1),
P_1=(1,a), R_1=(1,b), V_1=(1,c),                     (CPW5)

E=n=(a,a),           F=m=(b,b),       D=w=(c,c).     (CPW6)
```

Then `(CPW2)--(CPW4)` hold exactly.  In gauge notation they include

```text
E G_i E=H_i,          F G_i F=A_i,       [D,G_i]=1,  (CPW7)
```

where `A_i,H_i,G_i` are the factors of `P_i,R_i,V_i`.  Nevertheless

```text
DE=(ca,ca)                                               (CPW8)
```

has order three.  Thus `[D,E]!=1` and `DE!=1` even after the individual
private-Weyl commutators are imposed.

This is an exact scoped reservoir model of every displayed literal loop,
not a finite representation of the full EL20 presentation.  It shows that
the most direct same-chart relation `[w,V_i]=1` centralizes only the branch
Whitehead factor `G_i`; the diagonal native gauges `D,E,F` retain their
diagonal `S_3` holonomy.  A positive ESB row must mix the two branch
reservoir factors off the direct-product decomposition--for example, a
single ordinary word whose private coefficient enters both branch factors
and one of `n,m,w` without reducing to the identities in `(CPW3)`.

No Property T, Kazhdan input, local computation, trace hypothesis, or
literature theorem is used.

DERIVATION
complementary-private-weyl-s3-square-proof
