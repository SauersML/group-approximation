---
rg: 2
id: twisted-disagreement-return-commutator-reduction-proof
kind: route
title: Expand the soft mismatch carrier and compare it with the HNN commutator
target: twisted-disagreement-return-factors-through-localized-commutator
requires: []
---

Set `C=T^*AT` and `D=JB`.  Since `A,B,J` are involutions and `J` is
central, `D` is an involution.  Since `Q` reduces `C,B` and lies in the
negative `J` sector, it also commutes with `CB` and `JQ=-Q`.

First,

```text
4 X^*X
 = Q(1-BC)(1-CB)Q
 = Q(2-BC-CB)Q
 = Q(C-B)^*(C-B)Q.
```

Taking traces proves `(TDR4)` and also shows `||X||<=1`, since
`X=Q(1-CB)/2` is one half the difference of two contractions.

The corrected evaluation of the twisted word is

```text
U=A T D T^*.
```

Using `AT=TC`, `JX=-X`, and then expanding gives

```text
(U-1)TX
 = T(CJB-1)X
 = T(-CB-1)Q(1-CB)/2
 = TQ((CB)^2-1)/2.                                    (P1)
```

But

```text
(CB)^2-1=C(BC-CB)B,
```

so unitary invariance of normalized Hilbert--Schmidt norm proves `(TDR5)`.
Notice that no exact commutation of `C` and `B` was used: its defect is
exactly the return defect.

For the direct commutator word,

```text
(CBCB-1)Q=C(BC-CB)BQ.
```

As `Q` commutes with `B`, another unitary cancellation gives `(TDR6)`.
Finally `||C-B||<=2` implies `(TDR9)`.  Summing `(TDR9)` and pigeonholing
proves the asserted density bound, while the established finite-menu Fejer
argument applies to either family of wandering words.

For Britton reduction, expand

```text
g=t^(-1)a t b t^(-1)a t b.
```

The possible pinches are `t^(-1)a t` and `t b t^(-1)`; `(TDR1)` excludes
both, including at the boundary between consecutive powers.  Thus every
positive power of `g` is Britton reduced.  Likewise

```text
u=a t (Jb)^(-1)t^(-1)
```

is reduced because `Jb notin K`, and the boundary between powers is reduced
because `a notin L`.  Hence both words have infinite order.  The condition
`Jb notin K` follows from `J in K` and `b notin K`.

For approximate packet corrections, telescope the five unitary factors in
`A T (JB)^(-1)T^*`.  Inversion preserves normalized-HS distance and
multiplication by contractions does not increase it, giving `(TDR7)`.
The same standard telescoping estimate handles the fixed-length commutator
word.  Therefore `o(1)` exactification errors do not alter any asymptotic
conclusion.
