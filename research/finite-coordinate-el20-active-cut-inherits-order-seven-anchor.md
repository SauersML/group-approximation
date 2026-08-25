---
rg: 2
id: finite-coordinate-el20-active-cut-inherits-order-seven-anchor
kind: claim
title: A positive EL20 active cut inherits both native Whitehead--Hecke order-seven anchors
distinct_from:
  native-whitehead-hecke-head-has-order-seven-anchor: that proves the exact elementary-group word relation and its commutant-involution coercivity; this asks for the genuinely finite-coordinate cut on which the two analytic native occurrences inherit that relation with vanishing leakage.
  center-chain-common-source-authenticates-native-covariances: that asks for comparison with the fixed center-chain Hecke polars in canonical-trace models; this is quantified over arbitrary operator-norm EL20 active profiles and permits a model-dependent positive cut.
  tracial-word-authentication-is-regular-firewalled: that rules out a dimension-free tracial construction of such a cut; this explicitly requires a finite-coordinate operation with no extension to the regular finite von Neumann algebra.
---

**OPEN FINITE-COORDINATE ORDER-SEVEN INHERITANCE.**  Put

```text
R=L_(F_2)(1,2),             G=EL_20(R),
z=e_13(s_1t_1).
```

Let `pi_n` be arbitrary operator-norm asymptotic matrix representations of
`G` on a positive-density active core on which `z` survives.  Exactify the
fixed prefix-Pauli and center-chain packets.  Construct model-dependent
source and range projections `Q_n,P_n` with

```text
liminf tr_n(Q_n)>0,          tr_n(P_n)=tr_n(Q_n)+o(1), (OCI1)
```

and the two actual native unequal-scale occurrence maps `T_(i,n)` together
with Hecke-head maps `S_(i,n)`, `i=1,2`, on those same cuts, such that after
the allowed fixed label relabelings

```text
T_(i,n)=S_(i,n)D_(i,n)+o_2(1).                         (OCI2)
```

Here each `D_(i,n)` is an asymptotic self-adjoint unitary in the relevant
multiplicity commutant.  More importantly, the cut must inherit the literal
ordinary-word anchors

```text
(J_1B_2A_1)^7=1,
(J_2B_3A_2)^7=1                                      (OCI3)
```

from `native-whitehead-hecke-head-has-order-seven-anchor` with all
compression boundary terms tending to zero.  After the label factors in
`(OCI3)` are collected, this must give the quantitative estimates

```text
||D_(i,n)-Q_n||_(2,tr_n)
 <= C(max_(r in F)||pi_n(r)-1|| + leakage_n) -> 0,    (OCI4)
```

for one fixed finite relation menu `F`.  Equivalently, the compressed
seventh power is within the right side of `(OCI4)` of `D_(i,n)`, while the
ungauged compressed seventh power is within that bound of `Q_n`.

The same cut must retain the common source/range factorization and the two
mixed source-Pauli commutator estimates of
`center-chain-mixed-hecke-overlap-is-common-pauli-source`.  Thus `(OCI4)`
identifies both native transports with the two Hecke maps on one
positive-density carrier, rather than merely killing an abstract spectator
on unrelated packet summands.

This is the exact remaining positive input exposed by the order-seven
calculation.  The fixed group-algebra center-chain projection cannot be used:
it has nonvanishing literal Whitehead leakage in the regular representation.
The selection in `(OCI1)` must therefore depend on the finite matrix
coordinate, and its positive mass and boundary estimate must follow from
operator-norm relation defect, not canonical trace multiplicities, raw
dimension, or a finite invariant actor profile.  No Property `(T)`, Kazhdan
projection, or literature theorem is permitted.

Equivalently, after pulling both row leakages back to the common source, the
load-bearing new estimate is the arbitrary-profile version of `(OSC4)` from
`order-seven-anchor-stops-at-whitehead-compression-leakage`:

```text
L_n=sum_(i=1)^2
 Q_n v_(i,n)^*J_(i,n)(1-Q_n)J_(i,n)v_(i,n)Q_n,

tr_n(Q_n 1_((C delta_n^(2alpha)),infinity)(L_n))
 <= C delta_n^alpha.                                  (OCI5)
```

The low spectral cut of `(OCI5)` is required to have the positive relative
active mass in `(OCI1)`.  The established order-seven compression telescope
then supplies `(OCI2)--(OCI4)`; those lines specify the typing which the
estimate must preserve, rather than an additional independent analytic
hypothesis.

## Attempts

- The fixed center-chain `Q` fails: its literal Whitehead leakage is positive
  in the exact regular representation.
- Intersecting all fixed Whitehead translates reaches the largest common
  reducing corner computed in `native-whitehead-corner-collapses-hecke-flags`,
  where the quarter/eighth Hecke distinction collapses.
- Minimal atoms of any fixed finite actor packet are Morita-neutral by
  `binary-leavitt-finite-actor-minimal-atom-dichotomy`.  Thus `(OCI5)` must
  use a growing or genuinely coefficient-sensitive finite-coordinate cut;
  this attack is the current live seam.
