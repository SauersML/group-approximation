---
rg: 2
id: one-arm-return-of-complementary-q-child-stays-orthogonal
kind: claim
title: One a1 or b1 return keeps the complementary q child in an orthogonal label component
artifacts:
  - research/complementary-q-child-one-arm-split-proof.md
distinct_from:
  native-b1-completeness-factorization-stays-projective-times-c2: that stops with the complementary q child as a commuting C2 on two unused q subcorners; this adds each shortest a1/b1 return to an actual native coordinate and identifies the resulting three-label component.
  binary-leavitt-two-label-difference-occurrence-cells: that asks for odd label-only comparisons with the two actual native selector outputs on one positive Pauli carrier; this proves the obvious one-arm label-difference candidates act on the complementary p/q summands and remain disjoint from the native projective component.
  native-opposite-arm-return-has-finite-s6-model: that authenticates one s0/t0 arm through an opposite partial Whitehead and a marked return; this audits the degree-zero a1/b1 arms attached directly to the unused completeness child and allows both orientations simultaneously.
---

**ESTABLISHED ONE-ARM RETURN FENCE.**  Continue the notation of the shortest
`B_1` completeness factorization:

```text
P=x_(7,10)(p),        Q=x_(7,10)(q),
B'=x_(10,2)(b_1),     [P,B']=B_1,       [Q,B']=1.     (QAR1)
```

The two shortest attempts to return `Q` through one native degree-zero arm
are

```text
U=x_(10,2)(a_1),      [Q,U]=x_72(a_1)=:R_a,
V=x_(2,7)(b_1),       [V,Q]=x_(2,10)(b_1)=:R_b.       (QAR2)
```

They are genuine nonzero ordinary Steinberg incidences.  Moreover

```text
[P,U]=1,              [V,P]=1,                        (QAR3)
```

so each row selects exactly the formerly unused `q` child.  These are the
minimum one-arm return candidates requested by the coefficient table.

Neither couples that child to the old native projective component.  Split
the three involved ambient coordinates into their orthogonal cylinder
summands.  The old projective `SL_10(F_2)` head uses

```text
q@2,                 p@7,                 p@10,
```

whereas `(QAR2)` acts on the complementary labels

```text
p@2,                 q@7,                 q@10.       (QAR4)
```

With `U` alone or `V` alone, the new elementary-image factor is the finite
positive unitriangular group `UT_3(F_2)`.  If both are adjoined, the three
arrows form the complete directed three-cycle on `(QAR4)` and generate
`SL_3(F_2)`.  In every case this factor commutes with the old projective head
in the canonical elementary image.  Thus even both one-arm returns give

```text
SL_10(F_2) times SL_3(F_2)                             (QAR5)
```

after the harmless full two-arm enlargement.

The tensor product of the natural nonzero-vector representation of the
first factor with the left regular representation of the second is an exact
finite model of the completeness table, both returned arms, the marked-star
packet, and the adjacent native Whiteheads.  It has

```text
rank(P_z)=168*256,          rank(E)=168*64,
rank(F)=0,                                               (QAR6)
```

and every word in `(QAR1)--(QAR3)` is nontrivial where its coefficient is
nonzero.

The reason is structural: multiplication by `a_1` or `b_1` changes the
cylinder label.  Starting on the unused `q` summand of a coordinate whose
native label is `p`, one such arm lands on the unused `p` summand of an
actual q-labelled coordinate, not on its native `q` summand.  A second arm
closes the complementary three-label component rather than crossing back to
the old one.

Consequently the next viable occurrence must identify one of the two
orthogonal summands at a shared ambient coordinate through an object-erasing
payload row, or use a coefficient with a nonzero path from `(QAR4)` to the
old label set.  The two obvious single-arm `a_1/b_1` returns are not the odd
label-difference cells required by the shared-gauge compiler.

This is an elementary-image finite packet fence, not a representation of
the full infinite Steinberg group.  No Property `(T)`, canonical trace,
literature theorem, or computation is used.

DERIVATION
complementary-q-child-one-arm-split-proof
