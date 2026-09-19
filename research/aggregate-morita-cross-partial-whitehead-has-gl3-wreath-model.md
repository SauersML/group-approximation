---
rg: 2
id: aggregate-morita-cross-partial-whitehead-has-gl3-wreath-model
kind: claim
title: The first cross partial Whitehead mixes the returned GL3 packets but retains a finite wreath gauge
artifacts:
  - research/aggregate-morita-cross-partial-whitehead-gl3-wreath-proof.md
distinct_from:
  aggregate-morita-common-opposite-return-has-gl3-square-model: that stops with the two returned child packets in a direct product; this adjoins one literal balanced cross-coefficient Whitehead and a constant coordinate swap which conjugate native arms between those packets.
  cross-branch-partial-whiteheads-have-finite-wreath-gauge-model: that mixes the branch-resolved S3 packets generated only by the positive and reverse idempotent roots; this authenticates the mixer on the literal gauge-nonzero Morita arms and the returned GL3 packets.
  degree-zero-leavitt-core-has-locally-finite-marked-models: that fences arbitrary fixed menus confined to balanced coefficients; the occurrence here is balanced as a transporter but its two covariance rows are typed against the unbalanced native coefficients s_i and t_i.
---

**ESTABLISHED FIRST CROSS-PACKET FENCE.**  Retain the aggregate Morita
common-opposite table

```text
S_0=x_79(s_0),       S_1=x_(7,10)(s_1),
T_0=x_98(t_0),       T_1=x_(10,8)(t_1),
U_0=x_89(s_0),       U_1=x_(8,10)(s_1),
V_0=x_97(t_0),       V_1=x_(10,7)(t_1),              (MCP1)

C_i=[S_i,T_i]=x_78(q_i),
R_i=[U_i,V_i]=x_87(q_i),
N=C_0C_1=x_78(1),    D=R_0R_1=x_87(1).              (MCP2)
```

Put

```text
p=s_0t_1,                 r=s_1t_0,
K=x_78(p)x_87(r)x_78(p),
P=x_(9,10)(1)x_(10,9)(1)x_(9,10)(1),
H=PK.                                                     (MCP3)
```

The supports of `P` and `K` are disjoint.  Both are involutions, so `H` is
an involution.  Direct Leavitt multiplication gives the literal
coefficient-sensitive covariance rows

```text
HS_0H=U_1,              HU_1H=S_0,
HT_1H=V_0,              HV_0H=T_1.                    (MCP4)
```

Thus `H` is outside the branchwise `GL_3(F_2) times GL_3(F_2)`
factorization: it moves named nonidentity arms between its two factors.  It
is the smallest natural cross-packet occurrence after the common opposite
return--one cross partial Whitehead and one constant stabilization already
touch literal `s_0,s_1,t_0,t_1` occurrences in both directions.

There is a canonical second implementation which does transport both
complete packets.  Put

```text
K'=x_78(r)x_87(p)x_78(r),
u=p+r,
T=KK'=x_78(u)x_87(u)x_78(u),
J=PT.                                                    (MCP5)
```

Then `J` is an involution and

```text
JS_iJ=U_(1-i),          JT_iJ=V_(1-i),
JC_iJ=R_(1-i)                    for i=0,1.            (MCP6)
```

This is an exact identification of each positive child occurrence with the
opposite returned child in the other branch.  Comparing the two literal
implementations gives

```text
HJ=K'.                                                   (MCP7)
```

The comparison still does not force the relative implementation to be
trivial on the reservoir.

The added rows do not identify the two reservoir gauges.  Let

```text
K_3=GL_3(F_2)
```

and, in each copy, use

```text
S=e_12,      T=e_23,      C=e_13,
U=e_32,      V=e_21,      R=e_31,                     (MCP8)
```

where `e_ab=I+E_ab`.  Let `phi` be conjugation by the permutation matrix
which exchanges coordinates `1` and `3`.  Then

```text
phi(S)=U,      phi(T)=V,      phi(C)=R.                (MCP9)
```

In the finite wreath-type group

```text
G=((K_3 times K_3) semidirect <j>) times <z>,
j(g_0,g_1)j=(phi(g_1),phi(g_0)),
j^2=z^2=1,                 [z,G]=1.                  (MCP10)
```

put every branch-`i` name from `(MCP8)` in factor `i`, retain the diagonal
parents as in the common-opposite model, and send

```text
J -> j,             H -> zj,             K' -> z,
K -> 1,             T -> z,              P -> zj.     (MCP11)
```

Equations `(MCP1)--(MCP7)` hold exactly, including all matching and crossed
child commutators from the previous table.  In particular `(MCP7)` holds
while the relative gauge `K'` is the nontrivial central involution `z`.
The prescribed marked child remains

```text
C_1=(1,e_13) != 1.                                   (MCP12)
```

Hence even the full coefficient-sensitive cross-packet identification and
its comparison with one partial implementation upgrade the direct-product
escape only to a finite wreath escape with one central relative bit.  The
next live occurrence must make `K'` act nontrivially on a fixed named packet
factor, or otherwise compare the two implementations after removing this
central reservoir freedom; merely transporting every child across the
factors is insufficient.

This is a scoped occurrence-table model, not a finite representation of
the full binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
aggregate-morita-cross-partial-whitehead-gl3-wreath-proof
