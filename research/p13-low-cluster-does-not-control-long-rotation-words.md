---
rg: 2
id: p13-low-cluster-does-not-control-long-rotation-words
kind: claim
title: The robust P13 low cluster does not control escaping rotation words
distinct_from:
  p13-hodge-robust-rotation-gap: that proves the quantitative low/high split for the six substituted P13 words; this proves that the low side still gives no uniform control of arbitrary rotation words.
  literal-transport-gap-step-is-noneffective: that audits the non-effective declaration in the current Lean path; this gives an explicit one-dimensional counterfamily to the tempting direct robustification of its affine circumcenter proof.
  effective-transport-modulus: this is a no-go for one proof step, not a refutation of an effective full-base modulus.
---

For every integer `n>=1`, put `t_n=pi/n` and evaluate the literal
six-generator affine base on the one-dimensional Hilbert space by

```text
v1=v2=v3=1,       X=exp(i t_n),       Y=Z=1.             (LWD1)
```

All three translation-commutation relators and all nine affine action
relators hold exactly. Every one of the eight rotation relators has
operator-norm defect at most

```text
delta_n=6 pi/n.                                           (LWD2)
```

Under the checked P13 substitution, the six words have values

```text
(1,1,exp(-2 i t_n),1,exp(-3 i t_n),exp(3 i t_n)).
```

Consequently their rotation Laplacian satisfies the exact formula and bound

```text
Delta_n
 =|exp(-2 i t_n)-1|^2+2|exp(3 i t_n)-1|^2
 <=22 pi^2/n^2.                                          (LWD3)
```

Thus these vectors lie on the low side of the robust P13 split for all
sufficiently large `n`. Nevertheless the escaping rotation word

```text
r_n=(Z X Y)^n
```

acts as `-1`, and hence

```text
||r_n(1)-1||=2.                                          (LWD4)
```

The words are not an artificial repetition of a torsion element. In the
displayed integral rotation quotient, `A=ZXY` has upper-left block

```text
[[ 0, 1, 0],
 [ 0,-1,-1],
 [-1, 0, 0]]
```

with characteristic polynomial `s^3+s^2-1`; it has infinite order, and
the translations `A^n e_2` are pairwise distinct. Hence `r_n` are genuine
escaping conjugators for the translation normal form.

In particular there is no dimension-independent function tending to zero
with the rotation-relator defect and P13 energy that bounds the displacement
of **every** rotation word on a P13-low vector. The exact affine proof may
therefore not replace its rotation-fixed projection by the P13 low spectral
projection and then reuse uniform invariance under arbitrary translation
conjugators. A positive effective route must first obtain a full affine
spectral certificate or a robust relative-property-(T) estimate; ordinary
word telescoping cannot close this gate.

DERIVATION
[[p13-scalar-long-word-drift-proof]]
