# The full raw order-512 closure has trivial comb intersection

Date: 2026-08-13

## Outcome

Finite-subgroup Reynolds averaging cannot prove the coefficient-space
membership gate.  The entire finite subgroup carrying the raw double-Pauli
packet is disjoint from its comb conjugate, except for the identity.

Let

```text
K=<X0,X1,Z0,Z1,raw>.
```

The earlier exact audit gives

```text
|K|=512.
```

Using common-depth canonical keys for exact binary Leavitt-prefix elements,
the new audit computes

```text
|K intersect U* K U|=1.                              (TCI1)
```

The sole intersection element is the identity.  This strengthens the earlier
facts that the order-32 Pauli packet has trivial intersection with its comb
conjugate and that a smaller order-64 cell shares only one root sign.

## Consequence

The raw coefficient `C2^2` lies in the commutant/center of the finite raw
packet, while its transported copy lies in the corresponding algebra for
`U*KU`.  Equation `(TCI1)` shows that there is no common nontrivial finite
subgroup whose invariant-space conditional expectation could identify those
two coefficient algebras.

In particular, the following shortcut is closed:

```text
large finite raw packet
  + common finite intersection after comb transport
  + finite Reynolds exactification
  => coefficient-space membership.
```

The missing membership theorem from `TRUE_COEFFICIENT_EXPECTATION_GAP.md`
must instead use actual cross-chart kernel relators or the recovered
multiplication module.  Separate exactification of the two order-512 finite
subgroups leaves their relative multiplicity unitary completely unconstrained.

This is consistent with the complete `4 x 4` trace-flat transition table:
the two coefficient decompositions are fully transverse rather than sharing a
finite chart.

## Reproducible certificate

`experiments/atlas_raw_closure_comb_intersection.py` generates the bounded
order-512 subgroup and hashes both it and its comb conjugate after one common
exact prefix refinement.  Its checked output is
`experiments/atlas-raw-closure-comb-intersection.json`.  The one-core MSI run
finished in under ten seconds; no local code was run.

