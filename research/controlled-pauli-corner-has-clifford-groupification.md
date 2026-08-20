---
rg: 2
id: controlled-pauli-corner-has-clifford-groupification
kind: claim
title: A central-corner block becomes an honest group covariance after Pauli completion
artifacts:
  - experiments/controlled_corner_clifford_groupification.py
distinct_from:
  central-corner-block-is-not-a-group-word: that proves the additive block is not a word in the commuting control and payload alone; this adds conjugate Pauli partners and realizes only its conjugation action by a new group element.
  predicate-activated-cnot-routes-relative-pauli-halves: that realizes a CNOT router for a predicate commutator; this gives the diagonal CZ normal form of the controlled-corner operator and classifies every marked representation of its finite semidirect product.
---

Let `P` be the two-qubit extraspecial Pauli group

```text
P=<J,X1,Z1,X2,Z2 |
   J central, all generators involutions,
   [X1,Z1]=[X2,Z2]=J, all other commutators=1>.
```

The assignment

```text
theta(X1)=X1 Z2,  theta(Z1)=Z1,
theta(X2)=Z1 X2,  theta(Z2)=Z2,  theta(J)=J             (CPC1)
```

is an involutive automorphism. Hence the finite semidirect product

```text
G_CZ=P semidirect_theta <t | t^2=1>                   (CPC2)
```

is an ordinary finite group. On the irreducible `J=-1` Pauli module put

```text
c=(I-Z1)/2,        C_Z=(I-c)+c Z2.                    (CPC3)
```

Then `C_Z` is the standard controlled-Z involution and conjugation by `C_Z`
is exactly `(CPC1)`.

More generally, every finite-dimensional representation `rho` of `G_CZ` on
which `J=-I` has a unitary identification

```text
rho(p)=S(p) tensor I_M,       rho(t)=C_Z tensor V,     (CPC4)
```

where `S` is the unique four-dimensional spin representation of `P` and `V`
is a self-adjoint involution on the multiplicity space `M`. Consequently
every use of the controlled block **through conjugation of Pauli words** is
uniform in all representations: the factor `V` cancels. A use of `t`
itself, its spectral projections, or its trace is not uniform and retains the
uncontrolled multiplicity type `V`.

Thus Pauli completion gives a genuine escape from the additive-word barrier,
but only for covariance-only constructions. It neither asserts the literal
group identity `t=(1-c)+c Z2` nor selects one of the two extensions
`V=+I,-I`.

It also forces the control to be balanced. The Pauli partner `X1` exchanges
the two `Z1` signs, so each has half the marked trace. This is harmless for a
relative-Pauli child sign, but it prevents applying the construction to an
arbitrary-weight selector corner; see
`clifford-groupified-control-is-forced-balanced`.

Because `G_CZ` is fixed and finite, the same statement is robust after
finite-group flexible normalized-HS exactification: on the exactified marked
sector its Pauli covariance is exact, and the discarded/compression error is
controlled with constants independent of matrix dimension.
