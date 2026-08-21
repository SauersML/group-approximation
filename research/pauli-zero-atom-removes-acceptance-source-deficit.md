---
rg: 2
id: pauli-zero-atom-removes-acceptance-source-deficit
kind: claim
title: A unique Pauli spin control makes the zero-ancilla Gram source automatic
distinct_from:
  block-encoded-acceptance-still-needs-corner-return: that allows an arbitrary transport `PUQ` and therefore has a source-saturation deficit; this chooses the source directly in a unique finite spin type and removes that deficit.
  hecke-dilations-do-not-lock-capacity-gram: that finds a primitive-type source deficit for a general finite monomial dilation; this uses the unique marked irreducible of an extraspecial control packet and its full matrix commutant.
  gauge-pair-holonomy-needs-one-source-moment: that builds a context Hecke unitary with literal common source `Q`; this supplies the fixed control-atom factor for the cyclic acceptance unitary and leaves only its return moment.
---

Fix `m` control qubits and let `E_m` be the extraspecial Pauli group with
central involution `J_ctl`.  In the marked sector

```text
J_ctl=-I,                                               (PAZ1)
```

`E_m` has one irreducible representation, of dimension `2^m`.  Hence every
finite-dimensional exact marked representation has the form

```text
H_-=C^(2^m) tensor M,
E_m acts as Pauli_m tensor I_M.                         (PAZ2)
```

Let `Z_1,...,Z_m` be its commuting computational Pauli involutions and put

```text
P_0=product_(j=1)^m (I+Z_j)/2.                         (PAZ3)
```

Then

```text
P_0=|0^m><0^m| tensor I_M.                             (PAZ4)
```

Any operator commuting with the whole control Pauli group is

```text
I_(2^m) tensor b                                       (PAZ5)
```

by Schur's lemma.  In particular, if the original marked/capacity projection
`Q` belongs to a base packet commuting with the controls, then on `(PAZ2)`

```text
Q=I_(2^m) tensor q,
G=P_0Q=|0^m><0^m| tensor q,                            (PAZ6)
```

and exactly, for the normalized trace on the marked control sector,

```text
||G||_2^2=2^(-m) tau(Q).                               (PAZ7)
```

Thus the zero-control Gram source loses only one fixed factor determined by
the static game.  It has no source deficit and needs no HNN transport.

## Approximate fixed-packet form

In normalized-HS microstates, exactify the one fixed finite Pauli table.
The marked control sector then has the form `(PAZ2)` after the standard
flexible dimension correction.  Averaging the base words over `E_m` moves
them into the commutant `(PAZ5)` with squared error bounded by the fixed sum
of their named commutator defects.  Therefore `(PAZ7)` becomes

```text
||P_0Q||_2^2
 =2^(-m)tau(Q)+O(E_ctl^(1/2)),                         (PAZ8)
```

with a constant independent of the ambient matrix dimension.  If `Q` is a
fixed polynomial in already exactified commuting involutions, its projection
rounding contributes only another fixed `o(1)` term.

The use of the **full** Pauli control group matters.  A lone abelian control
Masa would let the base action vary independently from one computational
atom to another.  The transverse Pauli generators force all atoms into the
single matrix factor `(PAZ2)` and put every commuting source entirely in the
multiplicity algebra.

## Insert the block-encoded verifier

Use the same control qubits for the fresh-ancilla block encoding in
`block-encoded-acceptance-still-needs-corner-return`.  The controlled game
reflections and Hadamard/Clifford normalizers preserve the marked Pauli
sector, and their product satisfies

```text
P_0 W_game P_0=P_0 tensor T_game.                      (PAZ9)
```

For `G=P_0Q`, define the sole return scalar

```text
eta_0(Q)
 =||P_0Q||_2^2-Re tau(QP_0W_gameP_0Q).                (PAZ10)
```

The finite game contraction gives

```text
eta_0(Q)
 >=(1-rho)||P_0Q||_2^2
 >=(1-rho)2^(-m)tau(Q)-o(1).                          (PAZ11)
```

Consequently a matrix-only group-word estimate

```text
eta_0(Q)<=K E_rel+o(1)                                (PAZ12)
```

already pays the complete marked source mass.  The separate source deficit
`(BAE10)` has disappeared.

## Exact completeness and remaining obstruction

In the exact perfect tracial model, amplify by the marked spin control and
let the base BCS algebra act on the multiplicity factor.  The perfect Gram
vector is

```text
|0^m> tensor 1,
```

which is fixed by `W_game`.  Thus `(PAZ10)` vanishes on the exact witness,
and the native mark on the multiplicity factor remains nontrivial.  No
global identity `W_game=I` is imposed.

The exact finite packet/wreath audit is now in
`controlled-reflection-cell-has-free-orientation`.  The intended action and
the perfect-witness extension exist, but selection by `J_ctl=-1` alone does
not force `(PAZ9)`: every controller has a free multiplicity involution in
front of its acceptance projection.  An orientation Hecke moment is needed
to select the intended block.  Conditional on those moments, source mass is
no longer the analytic problem and `(PAZ12)` is the sole return interface.

Finite wreath naming alone does not prove `(PAZ12)`: it names `W_game`, while
`eta_0(Q)` couples that word to the original capacity source `Q`.  The D8
decoupling audit therefore survives only at the **return** layer, not at the
source-norm layer.  Before reaching that return layer, the finite controller
must additionally pay or eliminate the free orientation `(COR6)`; this is
an algebraic selected-type obstruction, distinct from source norm.

Equivalently, direct polarization gives

```text
2 eta_0(Q)=||(W_game-I)P_0Q||_2^2.
```

Thus no expanded verifier row remains.  The final matrix-only interface is
one capacity-gated block-unitary corner norm.
