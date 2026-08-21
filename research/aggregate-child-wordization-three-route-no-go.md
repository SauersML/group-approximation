---
rg: 2
id: aggregate-child-wordization-three-route-no-go
kind: claim
title: Tail cancellation, a Toeplitz corner, and a product of child words do not wordize the aggregate Schur child
distinct_from:
  raw-schur-generator-is-not-child-center: that identifies the corrected selector-controlled coefficient; this rules out three proposed ways of turning the whole corrected child carrier into one ordinary reflection word.
  recursive-clifford-tail-supplies-anchor-but-not-contraction: that constructs an exact same-gauge identity-outer occurrence; this shows that cancellation produces only the fixed local Clifford gate and does not perform selector control.
---

**SHARP ROUTE NO-GO.** None of the following three already available
operations constructs the ordinary aggregate reflection required in `(TSC7)`:

1. multiplying the recursive Clifford tail by its identity-outer anchor;
2. declaring the proper Toeplitz generators to be group words; or
3. multiplying the finite support-adaptive family of corrected child
   reflections.

This is not a no-go for every finite-matrix-only compiler. It isolates the
additional operation that such a compiler must provide.

## Tail cancellation is local, not selector controlled

The recursive identity is

```text
T_x A_x=(CZ_x tensor V_x)(I_x tensor V_x)=CZ_x tensor I.       (ACW1)
```

It removes the common multiplicity gauge exactly. In contrast, the actual
corrected child coefficient of a Schur packet is

```text
Q_f=sum_s e_s Q_s,
Q_s=q_(N+1) product_j q_j^(v_j(s)).                            (ACW2)
```

Here the selector-dependent vector `v(s)` is the Schur-complement output.
Every word in the elementary abelian `q`-MASA has one fixed normal form

```text
J^b q_(N+1)^epsilon product_j q_j^a_j.                         (ACW3)
```

so its `q`-exponent vector is independent of `s`. Central selector factors
can change only the scalar sign on the `s`-sector. Therefore, whenever
`v(s)` is not constant, no fixed word in this tail/MASA packet agrees with
all the `Q_s`. Equation `(ACW1)` supplies the fixed Clifford factor in one
row after a corrected child has been selected; it does not perform the
selection in `(ACW2)`.

## The Toeplitz proper corner cannot consist of group units

The binary Schur--Toeplitz envelope uses

```text
yx=1,                    1-xy=P !=0.                           (ACW4)
```

If `x,y` were ordinary group words, then they would be unitaries. In every
unitary representation, `YX=I` implies `Y=X^*` and hence `XY=I`, forcing
`P=0`. The approximate version is equally rigid: for unitary matrices,

```text
||I-XY||_2=||X(I-YX)X^*||_2=||I-YX||_2.                       (ACW5)
```

Thus the one-sided Toeplitz defect cannot stay macroscopically positive when
the reverse product is accurate. The Toeplitz endomorphism is a valid
algebraic placement of the child types, but its proper isometries are not an
ordinary-group wordization.

## A product of menu reflections records parity, not surplus

Let `R_i=I-2C_i` be two candidate child reflections. Their product is an
involution exactly when they commute: `(R_1R_2)^2=I` is equivalent to
`R_1R_2=R_2R_1`. In that case

```text
(I-R_1R_2)/2=C_1+C_2-2C_1C_2,                                (ACW6)
tr((I-R_1R_2)/2)=tr(C_1)+tr(C_2)-2tr(C_1C_2).                 (ACW7)
```

For a finite commuting menu the analogous product selects odd overlap
parity. Hence its trace is the desired additive sum only after an
orthogonality theorem. If the context child cuts do not commute, the
product is not even a reflection.

One may make the cuts orthogonal by putting them on private central tag
summands. That replaces the shared noncommuting BCS tuple by reducing
context copies. Transferring the robust shared forbidden mass to those
private summands is precisely the common-carrier/decoder statement that the
construction is not allowed to assume.

Consequently the finite family `(Q_s)_s` from the full `q`-MASA is useful as
a decoder menu but does not collapse to the single `R_C` of `(TSC7)` by
ordinary multiplication. A positive completion must add a genuinely
finite-matrix-only selected-sector or multiplicity operation which both
orthogonalizes the menu and proves its coverage from the original shared
BCS tuple. Exact perfect-model compatibility of the recursive tail remains
untouched.
