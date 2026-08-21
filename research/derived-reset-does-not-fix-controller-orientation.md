---
rg: 2
id: derived-reset-does-not-fix-controller-orientation
kind: claim
title: The equal-scale derived reset does not select a controller orientation
distinct_from:
  controlled-reflection-cell-has-free-orientation: that finds the free multiplicity involution in one controller cell; this computes the complete edge restriction matrix and tests the existing balanced derived reset against it.
  affine-selector-clifford-proves-derived-reset-bridge: that makes a genuine gauge translation derived while preserving the old and fresh Schur scales; this shows why the same incidence cannot select an extension character which is invisible on the Pauli edge.
  regular-gauge-orbit-contains-equal-scale-derived-d8-reset: that realizes a balanced reset translation on a four-point regular gauge orbit; the intended controller is not a balanced translation and can even be the identity on a perfect test sector.
---

Consider one control qubit and one system involution `r`.  Let

```text
E=<J,X,Z | J central, X^2=Z^2=J^2=1, [X,Z]=J>
```

and form the controller cell by adjoining an involution `c` with

```text
[r,E]=1, [c,Z]=[c,r]=1, c X c X=r.                    (DRC1)
```

The intended marked-spin action is

```text
c=P_0+P_1 r,             P_0=(1+Z)/2, P_1=(1-Z)/2.   (DRC2)
```

The balanced four-point derived reset of
`derived-lifted-gauge-reset-spin-bridge` cannot select `(DRC2)`.  The failure
is already visible in the exact restriction matrix.

## Complete restriction matrix

Fix the `J=-1` Pauli spin representation `rho` of `E`.  Since `r` commutes
with the cell, first fix an `r`-character `epsilon in {+1,-1}`.  If
`epsilon=+1`, `(DRC1)` makes `c` commute with both Pauli generators, so on
an irreducible extension

```text
c=u I,                         u in {+1,-1}.           (DRC3)
```

If `epsilon=-1`, both `c` and `Z` anticommute with `X` and commute with
`Z`; hence `cZ` commutes with the full Pauli spin and

```text
c=u Z,                         u in {+1,-1}.           (DRC4)
```

Write `sigma_(epsilon,u)` for these four two-dimensional controller simples
and `tau_epsilon=rho tensor epsilon` for the two edge simples of
`<E,r>`.  With rows ordered

```text
sigma_(+,+), sigma_(+,-), sigma_(-,+), sigma_(-,-)
```

and columns ordered `tau_+,tau_-`, the restriction matrix is exactly

```text
       [1 0]
       [1 0]
B_ctl= [0 1].                                          (DRC5)
       [0 1]
```

Thus the intended orientation `u=+1` and the opposite orientation `u=-1`
have identical restriction to every Pauli-and-system edge datum.  The
orientation is an extension character, not a Pauli spin coordinate.

## What the derived reset does to this matrix

The affine selector Clifford bridge has common edge restriction

```text
2 rho_15                                                   (DRC6)
```

on both old and fresh full selector characters.  Tensoring that fixed
packet with `(DRC5)`, or replacing one hyperbolic pair by its balanced
rank-swap pair, changes `(DRC5)` only by the same common factor:

```text
       [2 0]
       [2 0]
B_new= [0 2] tensor rho_15.                              (DRC7)
       [0 2]
```

In particular the two duplicated rows remain duplicated.  Equal-scale
Morita matching transports both controller orientations equally; it does
not select one of them.  This is not a missing rank calculation.  Any graph
of finite packets whose controller edge omits `c` factors through `(DRC5)`
and is blind to `u`.

The same conclusion follows from characters.  The twist

```text
c -> -c
```

is trivial on `<E,r>`.  The four-point reset makes its genuine reset
translation a commutator, but it does not make this quotient character of
the controller edge nontrivial on the edge.  Adding the reset packet
therefore cannot remove the twist.

## Literal four-point identification fails completeness

One might instead identify the controller itself with the four-point reset
translation `s`.  On the regular four-point gauge block, a nontrivial
translation is balanced:

```text
tr(s)=0.                                                (DRC8)
```

The intended controller has

```text
tr(c)=1/2 (1+tr(r))                                    (DRC9)
```

in the marked Pauli spin sector.  In particular, on a perfect test summand
where `r=I`, `(DRC2)` has `c=I` and trace one.  It cannot be the nontrivial
four-point translation.  Identifying the derived reset with the controller
would therefore destroy the exact perfect-witness extension rather than
orient it.

Identifying the reset with the hidden `u` is not an ordinary-word
alternative: `u` is obtained by dividing `c` by the additive corner operator
`P_0+P_1r`.  It is not a group word in the controller presentation.

## Derivedness alone still permits both orientations

Even adjoining new involutions `p,q` and the relation

```text
[p,q]=c                                                (DRC10)
```

does not select `(DRC2)`.  After countable amplification, for either
`u=+I` or `u=-I`, decompose the amplified space into the `c=+1` and `c=-1`
subspaces.  Put commuting involutions on the positive subspace and copies of
the two-dimensional `D_8` spin pair on the negative subspace.  Then
`(DRC10)` holds exactly for either orientation.  Hence the properly infinite
HALT completion absorbs the lift on both sides, while finite restriction
data still see the duplicated rows `(DRC5)`.

## A tempting balanced double pass does not close the finite packet

If a Hadamard lift had no multiplicity action, the balanced word

```text
H c H c
```

would cancel `u` and its zero-control corner would be `(1+r)/2`.  In an
arbitrary extension, however,

```text
H=H_0 tensor v,              c=(P_0+P_1r) tensor u,
```

with independent multiplicity involutions `u,v`.  The double pass retains
the quotient commutator

```text
v u v u.                                               (DRC11)
```

The affine derived-reset restriction calculation does not impose
`[u,v]=1`; it again matches the two extension modes at equal scale.  Thus
balancing the visible controller letter merely moves the missing datum to a
mixed controller--Hadamard relation unless the full conjugation table is
authenticated.

## Exact remaining datum

There are only two ways for this packet lane to continue:

1. include `c` (or an equivalent orientation tag) in the common edge and
   select the `u=+1` rows of `(DRC5)`; then the original source must be shown
   to saturate that refined edge type; or
2. impose a mixed finite table which kills `(DRC11)` and makes every word
   used by the acceptance block insensitive to the quotient action.

The first is exactly a new selected-type/source-authentication problem.  The
second is a full mixed-conjugation-table problem, not the existing derived
reset bridge.  Therefore the balanced four-point `D_8` construction does
not canonically orient the controller at equal Pauli spin scale without an
additional source or mixed-moment condition.
