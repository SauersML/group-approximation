---
rg: 2
id: hs-schur-packet-gap-amplification
kind: claim
title: Dinur powering and Schur composition amplify forbidden adjoint carrier mass
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
---

OPEN. Construct a finite group-word transformation on a shared-selector Schur
packet constraint graph with the following dimension-independent matrix
microstate guarantee. If `q` is total forbidden Hilbert mass before the
transformation and `q'` the exactified forbidden mass afterwards, then either
a bounded-overlap collection of named relators pays normalized-HS energy
`E`, or

```text
q' >= min(2q,alpha)-C sqrt(E).                                 (HPA1)
```

The output packet alphabet and every local word length must be bounded by
universal constants. Perfect tracial completeness must be preserved.

The intended construction follows Dinur's three stages:

1. expander preprocessing makes a local selector inconsistency occur on a
   controlled-density edge set;
2. graph powering copies that inconsistency through constant-length walks;
3. assignment-tester composition is implemented by fixed Schur--Clifford
   rank packets, returning to a bounded packet size.

The required conclusion is stronger than classical `(DGA1)`: selector
variables are shared noncommuting group words, local exactifications may use
different nearby corrections, and forbidden mass is a joint spectral trace.
The compiler must charge every disagreement between those corrections to HS
relator energy with bounded overlap.

## Attempts

- Apply classical powering directly to traces of context projections: this
  fails because independently exactified contexts need not induce one common
  selector assignment.
- Exactify the entire enlarged finite packet in one shot: its multiplication
  table grows with the powering/composition instance and loses a universal
  Gowers--Hatami error constant.
- Active attack: use the shared original selector words as the outer proof,
  the assignment tester only for constant-size local consistency, and the
  Schur rank jump as the rejection observable. The missing estimate is a
  robust composition lemma proving that inconsistent local corrections pay a
  bounded-overlap sum of the original commutator and identification relators.

