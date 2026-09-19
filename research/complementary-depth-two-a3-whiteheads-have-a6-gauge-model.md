---
rg: 2
id: complementary-depth-two-a3-whiteheads-have-a6-gauge-model
kind: claim
title: Complementary depth-two A3 Whiteheads retain an exact A6 reservoir gauge
artifacts:
  - research/complementary-depth-two-a3-a6-proof.md
distinct_from:
  full-completeness-opposite-menu-has-finite-gl5-fusion: that gives a three-copy finite occurrence model for a broad completeness menu; this writes the two complementary depth-two A3 cells and computes the smallest reservoir group simultaneously satisfying their opposite-root product and the native Whitehead/external-return S3 equations.
  reverse-product-whitehead-fold-has-finite-fusion: that establishes the coefficient identity multiplying the two branch Whiteheads; this places its aggregate Whitehead at the signed-Hecke coordinate pair and combines it with the literal native Weyl gauge table.
  depth-two-a3-return-is-gauged-external-root: that treats one A3 path whose product is already the constant external return; this keeps the two branch outputs separate inside their opposite-root Whiteheads until completeness is read.
---

**ESTABLISHED TWO-CELL GAUGE FENCE.**  Put `q_i=s_it_i`.  For
`i in {0,1}`, define the depth-two private coefficients

```text
a_i=s_i t_(i0),
b_i=s_(i0)t_(i1),
c_i=s_(i1)t_i.                                       (CTA1)
```

They obey

```text
a_i b_i c_i=q_i,             a_i c_i=0.              (CTA2)
```

Use two private A3 index paths ending in the common root position `(7,8)`.
Their two associator bracketings give the branch outputs

```text
P_i=x_78(q_i),                                        (CTA3)
```

while the shortcut carrying `a_i,c_i` is cross-zero.  Thus the individual
private address arms remain visible until the output `P_i` is formed.  Full
binary completeness is then the literal same-root return

```text
P_0P_1=x_78(q_0+q_1)=x_78(1)=:n.                     (CTA4)
```

Before using `(CTA4)`, put each branch output into the same opposite-root
family

```text
R_i=x_87(q_i),             V_i=P_iR_iP_i.             (CTA5)
```

Let `m=x_87(1)` and `w=nmn`.  Orthogonality and completeness give the exact
full-Leavitt ordinary-word relation

```text
V_0V_1=w.                                              (CTA6)
```

This is precisely the requested two complementary private-arm A3 cell: both
opposite-root words are formed before either branch is replaced by the
constant return, and their product reads completeness essentially.

It still does not force the literal Whitehead gauge and external-return
gauge to commute or cancel.  Let `D,E,F` be the reservoir factors of
`w,n,m`, so the native Weyl rows require

```text
D=EFE,                  F=DED.                         (CTA7)
```

Let `G_0,G_1` be the two branch-Whitehead reservoir factors.  Equation
`(CTA6)` adds

```text
G_0G_1=D.                                              (CTA8)
```

All these equations, including conjugacy of the three completeness packet
gauges, have the following exact finite solution in `A_6`:

```text
D  =(1 2)(4 5),          E  =(2 3)(5 6),
F  =(1 3)(4 6),
G_0=(1 2)(3 6),          G_1=(3 6)(4 5),
H  =(1 3 4)(2 6 5).                                   (CTA9)
```

Here

```text
G_0G_1=D,
H G_0 H^(-1)=G_1,     H G_1 H^(-1)=D,
H D H^(-1)=G_0,                                      (CTA10)
```

so `H` realizes the three-chart completeness fusion.  Meanwhile

```text
F=DED,                 D=EFE,
DE=(1 2 3)(4 5 6),                                    (CTA11)
```

and hence `DE` has order three.  In particular `[D,E]!=1` and `DE!=1`.

This is an exact scoped reservoir model of the full two-branch gauge table,
not a finite representation of the whole EL20 presentation.  It proves
that complementary A3 occurrence sharing, both private opposite roots,
completeness, the aggregate Weyl factorization, and all chart permutations
still do not provide the ungauged ESB bridge.  A positive row must force the
branch Whiteheads and the native `D,E` pair onto a stronger common-reservoir
relation than `(CTA7)--(CTA10)`--for example, a same-chart commutator
involving an individual private arm and `D` or `E`.

No Property T, Kazhdan input, local computation, trace hypothesis, or
literature theorem is used.

DERIVATION
complementary-depth-two-a3-a6-proof
