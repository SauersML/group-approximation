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

The added rows do not identify the two reservoir gauges.  Let

```text
K_3=GL_3(F_2)
```

and, in each copy, use

```text
S=e_12,      T=e_23,      C=e_13,
U=e_32,      V=e_21,      R=e_31,                     (MCP5)
```

where `e_ab=I+E_ab`.  Let `phi` be conjugation by the permutation matrix
which exchanges coordinates `1` and `3`.  Then

```text
phi(S)=U,      phi(T)=V,      phi(C)=R.                (MCP6)
```

In the finite wreath-type group

```text
G=(K_3 times K_3) semidirect <h>,
h(g_0,g_1)h=(phi(g_1),phi(g_0)),        h^2=1,         (MCP7)
```

put every branch-`i` name from `(MCP5)` in factor `i`, retain the diagonal
parents as in the common-opposite model, and send `H` to `h`.  Equations
`(MCP1)--(MCP4)` hold exactly, including all matching and crossed child
commutators from the previous table.  The prescribed marked child remains

```text
C_1=(1,e_13) != 1.                                    (MCP8)
```

Hence one actual coefficient-sensitive cross-packet transporter upgrades
the direct-product escape only to a finite wreath escape.  The next live
occurrence must distinguish the two factor-swapping implementations--for
example by comparing a returned child with a source child on one fixed
packet--rather than merely transport native arms across the factors.

This is a scoped occurrence-table model, not a finite representation of
the full binary Leavitt Steinberg group.  No Property `(T)`, Kazhdan input,
stability theorem, trace hypothesis, literature theorem, local computation,
or Lean compilation is used.

DERIVATION
aggregate-morita-cross-partial-whitehead-gl3-wreath-proof
