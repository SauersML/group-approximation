---
rg: 2
id: qutrit-third-cell-head-selector-is-h-centralizer-zero
kind: claim
title: The first third-cell head selector is binary-active but qutrit-zero
artifacts:
  - research/qutrit-third-cell-head-selector-proof.md
distinct_from:
  qutrit-two-mixed-cells-are-rf-three-are-full-leavitt: that locates the sharp group-theoretic threshold and the named Jacobson head; this tests the first new third-cell occurrence against the proper qutrit marginal.
  qutrit-jacobson-residual-has-fixed-polar-gap: that gives a terminal if a one-complement residual transport is authenticated; this proves the natural third-cell word does not authenticate such a transport.
---

Retain the two-cell head

```text
H=x_(c_2,c_1)(Q_0),       Q_0=1-s_0t_0=s_1t_1,
```

and add the new third-cell negative roots
`T_r=X_(2,r)=x_(c_0,c_2)(t_r)`. Then

```text
[T_r,H]=x_(c_0,c_1)(t_rQ_0)
       =1                         if r=0,
       =x_(c_0,c_1)(t_1)=B        if r=1.               (QTS1)
```

Thus `(QTS1)` is a genuine one-branch deletion of the Jacobson head.
For `E=(1-H)/2`, the first branch preserves the full head cut, while the
second forms a dihedral group `<H,T_1> isomorphic to D_8`. Its exact
compression is

```text
(E T_1 E)^2=F_+,
F_+=E(1+B)/2,              F_-=E(1-B)/2.                (QTS2)
```

The projections `F_+,F_-` are orthogonal, have sum `E`, and each carries
exactly half of every qutrit atom.

Nevertheless this is not the desired qutrit selector. Every coordinate
used by `G_3=EL_4(L)` lies in the fixed block of

```text
h=J^2Z.
```

Consequently

```text
[G_3,h]=1.                                               (QTS3)
```

Let `z_(rho,a)` be the nine character atoms of
`C=<J,Z>` and put `ell(rho,a)=2rho+a`. The complete
three-target table is

```text
operator       target condition                  squared block norm
H              (rho',a')=(rho,a)                         1/9
T_0,T_1,B      ell(rho',a')=ell(rho,a)                   1/27
T_0E,T_1E      ell(rho',a')=ell(rho,a)                   1/54
E T_1 E        ell(rho',a')=ell(rho,a)                   1/108. (QTS4)
```

All omitted blocks are zero. In the last row the three blocks sum to the
half-head source mass `1/36` on each source atom.

For the proper qutrit row

```text
e_a=z_(1,a),       q=e_0+e_1+e_2,
R=e_0+e_1,         q-R=e_2,
```

the three values `ell(1,a)=2+a` are distinct. Therefore `(QTS3)` gives

```text
e_b v e_a=0 for a!=b and every v in G_3,
(q-R)vR=0.                                              (QTS5)
```

The formal Hall endpoint would compare

```text
tau(ER)=1/9,                 tau(E(q-R))=1/18.           (QTS6)
```

A full-source partial isometry from `ER` into one complement carrier
would violate trace by `1/18`. But the candidate compression in
`(QTS5)` is zero. Before the qutrit cut, `E T_1 E` has polar support `F_+`, half of
`E`. Its overlap energy on `R` is `tau(F_+R)=1/18`; because
`F_+` need not commute with `R`, this is not the rank of a cut-down
polar support. The decisive no-go here is instead the exact vanishing
`(q-R)vR=0` for every `v in G_3`.

The finite-presentation status is positive. The binary Leavitt algebra
has a finite ring presentation, so the Krstic--McCool finite-presentation
theorem gives a finite presentation of `G_3=EL_4(L)`. If `F_q` is the
finite qutrit packet, the one-chart theorem and `(QMT3)` give

```text
<F_q,G_3>=EL_28(L),                                     (QTS7)
```

which is finitely presented by the same theorem. This is a mathematical
finite-presentation statement; no new Lean artifact is asserted.

A live selector must therefore leave the `h`-centralizer. The exact next
object is one scalar element `g in GL_28(F_2)-C_K(h)` which preserves or
controls the named head carrier but makes
`e_2 g(e_0+e_1)` nonzero. No word confined to the three mixed cells can
do so.
