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

`classical-pcp-gap-is-not-tracial-pvm-gap` shows that this statement cannot be
proved by simply applying Dinur's popular-assignment argument to the local
PVMs. Dinur amplification remains the outer incidence architecture only. The
soundness step must be quantum and dimension-sensitive; Tailored-MIP answer
reduction or Schur multiplicity transport must supply the missing global
consistency.

The Schur layer itself is now completely audited and contributes no
amplification.  `finite-local-schur-extension-preserves-forbidden-mass`
shows that every finite-dimensional selector representation extends all
context-local rank packets after one finite amplification, with every local
packet row exact and with

```text
q'=q.                                                        (HPA2)
```

A rational direct sum of one allowed and one forbidden scalar assignment
then refutes `(HPA1)` for `0<q<alpha/2` if `E` contains only those local
rows.  Therefore every factor-two gain in `(HPA1)` must be supplied by the
new cross-context preprocess/powering/answer-reduction relations.  Fixed
Schur--Clifford exactification is only the bounded-alphabet rejection
readout.

This means the frontier claim is not a smaller packet inequality.  Its
load-bearing content is a perfect-completeness, constant-loss tracial
quantum-PCP synchronization theorem: independently exact context
corrections must be reconciled on the shared noncommuting selector words, or
their disagreement must pay a bounded-overlap ordinary-word energy.  The
packet algebra after that synchronization is already in hand.

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
- Packet-only composition or larger local rank gates: refuted by
  `finite-local-schur-extension-preserves-forbidden-mass`; finite
  amplification clears every local divisibility constraint while preserving
  normalized forbidden mass exactly.
