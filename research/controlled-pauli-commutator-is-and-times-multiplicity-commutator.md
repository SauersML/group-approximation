---
rg: 2
id: controlled-pauli-commutator-is-and-times-multiplicity-commutator
kind: claim
title: Controlled Pauli commutators compute conjunction exactly and expose only the external multiplicity commutator
artifacts:
  - research/artifacts/reverse-kleene-multiplicity-holonomy-audit-2026-08-20.md
distinct_from:
  controlled-pauli-corner-has-clifford-groupification: that classifies one controlled gate and shows its multiplicity factor cancels under covariance; this computes a nonlinear phase from two gates and identifies the exact two-implementer residue.
  controlled-central-phase-finite-group-barrier: that rules out prescribing an arbitrary Boolean truth table by one scalar central phase; this obtains an AND-supported phase as a commutator of noncommuting reversible gates.
---

Let `P,Q` be commuting projections which commute with involutions `X,Z`, and
assume the group commutator `XZX^(-1)Z^(-1)=J` is a central involution.  The
controlled Pauli involutions

```text
U_P=(1-P)+PX,             V_Q=(1-Q)+QZ                  (CPM1)
```

satisfy the exact nonlinear identity

```text
[U_P,V_Q]=(1-PQ)+J PQ.                                  (CPM2)
```

Thus an ordinary group commutator carries the Pauli phase precisely on the
joint active, or Boolean-AND, sector.

Now fix one irreducible finite packet representation `S` and suppose two
group implementers preserve its isotypic carrier.  After identifying that
carrier with `H_S tensor M`, Schur's lemma gives

```text
U=C_U tensor R,              V=C_V tensor T,            (CPM3)
```

where `C_U,C_V` are fixed packet implementers and `R,T` are arbitrary
multiplicity unitaries.  Their commutator is

```text
[U,V]=[C_U,C_V] tensor [R,T].                           (CPM4)
```

Hence covariance relations alone do not certify the Boolean phase: the
external factor `[R,T]` can change it.  Conversely, if the construction
forces `R` and `T` to commute--in particular if both gates have the same
multiplicity factor--then `(CPM4)` reduces exactly to the desired packet
commutator tensored with the identity.  The remaining reversible-circuit
groupification problem is therefore multiplicity-commutator cancellation,
not reconstruction of selector characters.

There is an ordinary-word realization which avoids naming the control
projections.  Let `S,T` be commuting selector involutions commuting with
the Pauli involutions `X,Z,J`, and impose on involutions `U,V`

```text
[U,S]=[U,T]=[U,X]=1,          UZU=SZ,
[V,S]=[V,T]=[V,Z]=1,          VXV=TX.                (CPM5)
```

On the marked sector `J=-1` and the selector sector
`S=(-1)^a,T=(-1)^b`, Schur's lemma gives

```text
U=X^a tensor A_(a,b),         V=Z^b tensor B_(a,b),

[U,V]=J^(ab) tensor [A_(a,b),B_(a,b)].               (CPM6)
```

Thus `(CPM5)` groupifies the AND-supported Pauli phase by ordinary group
relations, but still leaves exactly one multiplicity-gauge commutator on
each selector sector.  Taking `T=GH` for commuting payload involutions
`G,H` makes `b=1` the payload-mismatch bit.  If the multiplicity commutator
is independently locked, the relation `[U,V]=1` forbids exactly the sector
where the selector is active and the payloads disagree.  The word syntax
therefore reduces selector-gated equality to the open finite-matrix gauge
lock; it does not supply that lock.
