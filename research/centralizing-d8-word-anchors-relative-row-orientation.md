---
rg: 2
id: centralizing-d8-word-anchors-relative-row-orientation
kind: claim
title: One centralizing D8 word anchors the relative orientation while leaving whole-row multiplicity free
distinct_from:
  partial-swap-row-orientation-cycle-needs-one-anchor: that separates harmless whole-row signs from the harmful relative grading twist and proves an unanchored cycle has a global two-fold ambiguity; this supplies the missing ordinary-word anchor itself.
  controlled-reflection-cell-has-free-orientation: that exhibits a free multiplicity involution in a fresh-control cell; this deliberately leaves a common transported multiplicity involution free and proves it is harmless for every anchored partial-swap row.
  finite-role-packet-cannot-supply-hybrid-predicate-row: that rules out a universally scalar nonlinear hybrid row in a finite regular packet; this packet is only the tautological orientation anchor and makes no nonlinear predicate table.
---

Let

```text
D_8=<z,j,y | z^2=j^2=y^2=1, y central, zj=yjz>,
```

and adjoin one involution `e` with

```text
e^2=1, [e,z]=[e,j]=1.                                (AOR1)
```

Thus the anchor packet is just `D_8 times C_2`.  It has a retraction onto
the original marked packet, given by `e -> 1`, so adjoining it cannot kill
the central mark `y` or obstruct any exact model of the marked base.

The word `e` is the tautological orientation.  Its relative `z`-twist is
the word `ze`.  In the packet one has the exact identities

```text
[e,j]=1,
[ze,j]=ze j ze j=zjzj=y.                              (AOR2)
```

Consequently the wrong relative orientation pays exactly the marked-word
distance in every unitary representation:

```text
||[ze,j]-1||_2=||y-1||_2.                             (AOR3)
```

In particular it cannot be hidden by spectator amplification.  On the
`y=-1` spin sector the wrong commutator is `-1`, hence has squared
normalized Hilbert--Schmidt cost four on that sector.

## The anchor need not select a scalar multiplicity character

Let an exact representation be split by the grading `Z` and write

```text
J=[[a,S],[S^*,d]],
E=diag(U,V).                                          (AOR4)
```

The anchor relations imply

```text
US=SV.                                                (AOR5)
```

They do not force `U` and `V` to be scalar, and no such selection is
needed.  If a row

```text
D=diag(A,B)
```

also commutes with `e`, then `U` commutes with `A`, `V` commutes with `B`,
and

```text
(UA)S-S(VB)=U(AS-SB).                                 (AOR6)
```

Thus multiplication of a row by the common anchor preserves its complete
partial-swap energy exactly.  The anchor may carry an arbitrary transported
whole-row multiplicity involution; only its relative `z`-orientation is
fixed.  This is precisely the quotient by the harmless whole-row gauge
identified in `partial-swap-row-orientation-cycle-needs-one-anchor`.

For a fixed finite row list, the extra commutation relators `[e,d_r]=1`
are compatible with every perfect model by taking `e=1`.  Therefore the
same harmless common gauge can be used while propagating orientation from
the anchor to the row packets.

## Dimension-free approximate estimate

Suppose first that `Z,J,E` are exact self-adjoint involutions.  Put

```text
delta_ej=||EJEJ-I||_2,
delta_ez=||EZEZ-I||_2,
delta_y =||ZJZJ-Y||_2.
```

Moving the first `E` successively past `J` and `Z` gives

```text
||ZEJZEJ-Y||_2<=delta_ej+delta_ez+delta_y.             (AOR7)
```

Hence

```text
||ZEJZEJ-I||_2
 >=||Y-I||_2-delta_ej-delta_ez-delta_y.               (AOR8)
```

All constants are independent of matrix dimension.  For arbitrary
approximate involutions, spectral rounding and exactification of the fixed
sixteen-element packet add only a dimension-independent `o(1)` term.
Equivalently, `(AOR8)` follows directly from a fixed van Kampen diagram for
`[ze,j]y^-1`; its area does not depend on a game, a predicate, or matrix
dimension.

## Exact frontier after the anchor

This closes the **one-anchor** subproblem.  It does not construct a hybrid
predicate row.  A remaining compiler must still transport each selected
row's relative orientation bit to this anchor without requiring that one
ordinary finite-packet word realize the nonlinear truth table on the whole
marked regular sector.  Once such relative comparisons are supplied,
`(AOR2)--(AOR8)` remove the simultaneous `z`-twist and `(AOR6)` shows that
the residual whole-row multiplicity action is harmless.

## Attempts and firewalls

- **Set the anchor equal to the identity.**  This is legal but stronger
  than necessary.  It obscures the useful fact `(AOR6)` that arbitrary
  transported whole-row multiplicity is harmless.
- **Demand that the anchor be scalar on the full marked regular packet.**
  Unnecessary, and it would recreate a selected-type problem.  The finite
  relations only fix the relative grading bit.
- **Claim that the anchor also supplies the nonlinear row.**  It does not.
  The regular-packet no-go for a universally oriented hybrid predicate row
  remains intact.
- **Use only an unanchored cycle.**  The simultaneous multiplication of
  every row by `z` survives all pairwise comparisons.  Equation `(AOR2)` is
  the one absolute mixed commutator which breaks that symmetry.
