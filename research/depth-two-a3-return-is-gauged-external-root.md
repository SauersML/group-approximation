---
rg: 2
id: depth-two-a3-return-is-gauged-external-root
kind: claim
title: The first nonseparated depth-two A3 return is still the gauged external root
artifacts:
  - research/depth-two-a3-external-return-proof.md
distinct_from:
  asymmetric-depth-two-fold-return-retains-external-gauge: that folds three private leaves additively inside one root subgroup; this uses a genuinely composable three-edge A3 path with a nonconstant middle matrix unit and keeps both associator bracketings and a literal cross-zero shortcut.
  tagged-a3-associator-cell-has-finite-positive-root-model: that treats a general positive tagged payload cell for the chromatic program; this places the marked A3 output at the coordinate-matched signed-Hecke external return and computes the gauge of the resulting one-Whitehead moving bridge.
  native-weyl-return-gauges-have-s3-model: that starts from the external return and its native Weyl expansion; this proves that the new depth-two A3 factorization does not add a reservoir relation beyond that existing S3 interface.
---

**ESTABLISHED NONSEPARATED A3 FENCE.**  Put

```text
alpha=t_00,          beta=s_00t_01,          gamma=s_01.
```

The binary Leavitt relations give the full depth-two table

```text
alpha beta=t_01,       beta gamma=s_00,
alpha beta gamma=1,    alpha gamma=0.                 (AER1)
```

On the root path `7 -> 10 -> 11 -> 8`, let

```text
A=x_(7,10)(alpha),
B=x_(10,11)(beta),
C=x_(11,8)(gamma),
G=x_(10,8)(gamma).                                    (AER2)
```

This is genuinely nonseparated: the middle coefficient `beta` is consumed
on both sides of the A3 cell.  The ordinary Steinberg relations and `(AER1)`
give

```text
[[A,B],C]=x_78(1),
[A,[B,C]]=x_78(1),
[A,G]=1.                                              (AER3)
```

Thus both Hall--Witt/associator paths produce the coordinate-matched external
return while the shortcut using the same private `gamma` arm is exactly
cross-zero.  This is the smallest literal depth-two marked-versus-zero A3
table on the signed Hecke coordinates.

Nevertheless, if `P` denotes either nested commutator in `(AER3)`, then the
full-group equality

```text
P=x_78(1)                                              (AER4)
```

means that on the signed Hecke carrier

```text
P|_Q=N_78 tensor E                                    (AER5)
```

with exactly the old uncontrolled external-return gauge.  Let `J=J_1` and
form the one-moving-occurrence bridge

```text
K=JP:QH -> JQJ^(-1)H.                                 (AER6)
```

After removing fixed label maps, its reservoir factor is `DE`, where `D` is
the Whitehead gauge.  The two associator bracketings and the cross-zero row
do not change that parity: `A,B,C,G` do not individually preserve `Q`, so
they do not define same-Hecke-carrier gauges which may be counted or
cancelled.  Conjugating the entire A3 table by `J` gives only the old
naturality equation

```text
E'=DED^(-1).                                           (AER7)
```

At this returned-occurrence interface the exact finite gauge assignment

```text
D=(1 2),             E=(2 3) in S_3                  (AER8)
```

satisfies `(AER4)--(AER7)` while `DE=(1 2 3)` is nontrivial.  The internal
A3 identities merely give two literal factorizations of the operator already
assigned gauge `E`; they impose no additional equation on `(D,E)`.

This is a scoped fence on using the associator, its cross-zero shortcut, and
one output Whitehead/Singer occurrence.  It is not a finite representation
of the whole EL20 presentation.  A positive mixed-channel cell must put the
Whitehead or another opposite-root occurrence on an individual private A3
arm before `(AER4)` collapses the path to `x_78(1)`, and must create a closed
same-carrier relation not reducible to conjugation of the total output.

No Property T, Kazhdan input, computation, trace hypothesis, or literature
theorem is used.

DERIVATION
depth-two-a3-external-return-proof
