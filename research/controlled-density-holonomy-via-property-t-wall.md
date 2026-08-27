---
rg: 2
id: controlled-density-holonomy-via-property-t-wall
kind: route
title: Pay controlled Schur flip density through the property-T compressor wall
target: controlled-reset-needs-positive-density-holonomy
requires:
  - controlled-pauli-corner-has-clifford-groupification
  - clifford-groupified-control-is-forced-balanced
  - schur-packet-flips-realize-predicate-cocycle
  - schur-packet-as-positive-density-compressor-wall
  - schur-wall-in-property-t-compressor-pays-hs-energy
  - finite-depth-contractive-computation-ladder
---

Use the balanced relative-Pauli halves for local controlled covariance and the
commuting Schur flip square for the projective multiplicity bit.  Place the
same forbidden packet across the property-`(T)` compressor.  The wall theorem
produces an adjoint subspace whose normalized density is bounded below by the
square of the forbidden carrier mass, while positive-density commutant
no-growth bounds that subspace by the global relator defect.

Thus every controlled forbidden mass `q_n` obeys

```text
q_n^2 <= C E_local,n.                                  (CDH1)
```

before the local context is separated from the shared BCS tuple.  Substitute
this payment into the finite controlled branch ledger.  Because the number of
cells is fixed, the square-root losses sum into one fixed constant and the
finite-depth contraction theorem supplies the energy floor.  The exact
tracial extension in the compressor-wall placement gives the completeness
clause of the target.

The open content of this route is entirely
`schur-packet-as-positive-density-compressor-wall`: the local covariance,
projective square, density-to-energy endpoint, and finite-depth ledger are
already established.

