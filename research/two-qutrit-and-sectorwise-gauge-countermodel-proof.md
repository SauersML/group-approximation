---
rg: 2
id: two-qutrit-and-sectorwise-gauge-countermodel-proof
kind: route
title: Decompose the controlled commutator over the four intrinsic selector sectors
target: two-qutrit-and-cell-retains-sectorwise-pauli-gauge
requires:
  - two-qutrit-controlled-bases-give-proper-multipath-marginal
  - controlled-pauli-commutator-is-and-times-multiplicity-commutator
---

The atoms `p_(a,b)` are pairwise orthogonal. Therefore the two sums in
`(TAG1)` commute, and their product retains exactly the atom common to
both index sets:

```text
ST
 =(sum_b p_(0,b))(sum_a p_(a,0))
 =p_(0,0).
```

The nine atoms have rank one in the marked spin block. Hence `S` and
`T` have rank three, their intersection has rank one, and elementary
inclusion--exclusion gives

```text
rank(E_11)=1,
rank(E_10)=rank(S)-rank(ST)=2,
rank(E_01)=rank(T)-rank(ST)=2,
rank(E_00)=9-3-3+1=4.
```

This proves `(TAG2)--(TAG3)`.

Because the `E_st` are orthogonal and sum to `q`, the formulas
`(TAG4)` define block-diagonal involutions. The gauge factors commute with
the selector packet and label factors, so the controlled label covariance
is unchanged. More explicitly,

```text
U Z_l U=(1-2S) Z_l,
V X_l V=(1-2T) X_l,                                    (TAG7)
```

while `U` commutes with `S,T,X_l` and `V` commutes with
`S,T,Z_l`. Thus these are the ordinary controlled-Pauli relations with
selector involutions `1-2S` and `1-2T`.

On the sector `E_st`, the commutator of the label factors is

```text
[X_l^s,Z_l^t]=(-1)^(st).
```

The commutator of the gauge factors is independently

```text
[X_g^(st),Z_g^(st)]=(-1)^(st).
```

Their product is one on every sector, proving `(TAG5)`. On the active
sector `E_11`, however, the gauge factors are `X_g,Z_g` and their
commutator is `-1`. In normalized Hilbert--Schmidt norm on that sector,

```text
||[X_g,Z_g]-1||_2^2=4.                                  (TAG8)
```

Since `rank(E_11)=1`, this is a positive-rank exact countermodel, not a
zero-carrier degeneration. Tensoring spectators preserves every equality
and the same normalized sector defect.

Thus all selector, conjunction, shared-label, controlled covariance,
involution, and commuting-total-commutator relations hold exactly while the
active multiplicity gauge is maximally noncommuting. Any relation that
eliminates this model must compare the multiplicity occurrences across
selector sectors or with an independently authenticated identity-label
occurrence. That comparison is additional to the local AND cell.
