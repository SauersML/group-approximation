---
rg: 2
id: doubled-controllers-do-not-preserve-game-gap
kind: claim
title: Orientation-invariant doubled controllers admit internal rotations which erase the game gap
distinct_from:
  controlled-reflection-cell-has-free-orientation: that finds one multiplicity involution in an unbalanced controller; this cancels the scalar orientation but finds a new quotient commutator in the doubled controller word.
  derived-reset-does-not-fix-controller-orientation: that proves the balanced derived reset cannot select the controller extension row; this gives an exact finite-dimensional countermodel showing why leaving the extension action unselected destroys strict cyclic acceptance.
  finite-game-gap-makes-the-cyclic-acceptance-compressor-strict: that proves strict contraction for the undressed product of acceptance projections; this shows that arbitrary range-preserving intertwiners between those projections invalidate the conclusion.
---

For one test let `r` be its reflection and put

```text
Q=(I+r)/2.                                              (DCG1)
```

Let `c` be the controller of
`controlled-reflection-cell-has-free-orientation`, and let `h` be a
Hadamard lift on the control Pauli qubit.  In an arbitrary exact marked-spin
representation their normal forms are

```text
c=(P_0+P_1r) tensor u,
h=H tensor v,                                          (DCG2)
```

where `u,v` are multiplicity involutions commuting with `r`.  There is no
relation in the separate finite tables which makes `u` commute with `v`.

The natural orientation-invariant double pass is

```text
B=(c h)^2.                                             (DCG3)
```

Both visible lift letters occur twice, so all one-dimensional sign twists
cancel.  Put

```text
w=(uv)^2.                                              (DCG4)
```

On the `r=+1` sector the spin part of `(DCG3)` is `H^2=I`.  On the `r=-1`
sector it is

```text
(ZH)^2=[[0,1],[-1,0]].                                 (DCG5)
```

Consequently, exactly,

```text
P_0 B P_0=P_0 tensor wQ.                               (DCG6)
```

The scalar orientation has disappeared, but it has been replaced by the
quotient commutator `w`.  It preserves the accepted subspace because
`[w,r]=1`; it need not be scalar there.

## Exact loss of strict cyclic contraction

Take the Gram multiplicity space `K=C^3` and the three acceptance
projections

```text
Q_1=proj span(e_1,e_2),
Q_2=proj span(e_2,e_3),
Q_3=proj span(e_3,e_1).                                (DCG7)
```

Their rejection projections are the three coordinate lines, so with equal
weights

```text
(1/3) sum_j ||(I-Q_j)xi||^2=(1/3)||xi||^2.            (DCG8)
```

Thus the undressed game has a fixed Rayleigh gap `lambda=1/3`, and the
cyclic product `Q_3Q_2Q_1` is a strict contraction.

Let `w_1` be the quarter-turn in `span(e_1,e_2)` sending `e_1` to `e_2`
and the identity on `e_3`.  Let `w_2` be the quarter-turn in
`span(e_2,e_3)` sending `e_2` to `e_3` and the identity on `e_1`.  Put
`w_3=I`.  Every `w_j` commutes with `Q_j`, but

```text
w_3Q_3 w_2Q_2 w_1Q_1 e_1=e_3.                        (DCG9)
```

Hence

```text
||w_3Q_3 w_2Q_2 w_1Q_1||_op=1.                       (DCG10)
```

This is an exact controller model, not an arbitrary dressing.  A planar
quarter-turn is `(uv)^2` for two reflections `u,v` whose axes differ by
`pi/8`.  Choose those reflections inside `Q_jK` and use the identity on its
orthogonal complement.  They are multiplicity involutions commuting with
`r_j=2Q_j-I`, exactly as required by `(DCG2)--(DCG4)`.

With one fresh control per test, `(DCG6)` makes the all-zero corner of the
product of doubled controller words equal

```text
w_3Q_3 w_2Q_2 w_1Q_1,                                (DCG11)
```

so `(DCG10)` is a direct counterexample to retaining the strict game gap.
The internal rotations move a vector from one pairwise intersection to the
next even though the three accepted subspaces have zero common
intersection.

This also explains why controlling only one-dimensional character twists is
insufficient.  Scalar signs in front of the `Q_j` would not affect the norm;
higher-dimensional quotient actions inside `Q_jK` do.

## Orientation-free Hecke salvage

The double pass does give a useful covariance-only projection.  Define

```text
E_j=B_j^* P_(0,j) B_j.                                (DCG12)
```

The multiplicity factor cancels under conjugation, and

```text
P_(0,j) E_j P_(0,j)=P_(0,j) tensor Q_j.               (DCG13)
```

If `P` is the joint zero-control projection, then inserting `P` between the
fresh-control factors gives

```text
P E_m P E_(m-1) P ... P E_1 P
 =P tensor (Q_mQ_(m-1)...Q_1).                        (DCG14)
```

Thus the original strict contraction survives exactly at the **Hecke
projection-product** level, with no orientation selection.

But `(DCG14)` is not one ordinary unitary word.  Each `E_j` is the additive
corner `(I+B_j^*Z_jB_j)/2`.  Replacing it by the reflection
`2E_j-I=B_j^*Z_jB_j` loses positivity and returns to the product-of-
reflections phase-cancellation obstruction.  Naming `(DCG14)` as one
coefficient returns to the existing root-to-coefficient/kernel-reflection
interface.

## Minimal ordinary-word repair

An ordinary doubled-controller block can retain the game gap only if the
mixed controller--Hadamard table forces every `w_j` in `(DCG4)` to be a
scalar, or forces all of them to cancel as one common quotient action.  The
separate Pauli, controller, Clifford, and balanced derived-reset restriction
tables do not do this.  It is a full mixed-conjugation-table condition.

Therefore orientation-invariant doubling has the following exact status:

- one-dimensional controller signs: canceled;
- strict positive compressor as a Hecke product: preserved by `(DCG12)--(DCG14)`;
- strict compressor as the zero corner of ordinary doubled words: **false**
  by `(DCG7)--(DCG11)`;
- remaining repair: authenticate the mixed quotient commutators, or return
  to the nonunitary Hecke coefficient interface.
