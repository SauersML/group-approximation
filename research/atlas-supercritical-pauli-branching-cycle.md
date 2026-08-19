---
rg: 2
id: atlas-supercritical-pauli-branching-cycle
kind: claim
title: The atlas Pauli carriers contain a supercritical finite branching cycle
artifacts:
  - docs/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - docs/TRUE_RAW_PAULI_COEFFICIENT_CUT.md
distinct_from:
  atlas-one-cut-finite-multiplicity-extraction: that forces one transported large carrier back under one smaller cut; this target permits the return path to wander through finitely many coefficient sectors and only asks that the resulting branching graph be supercritical.
---

For the fixed finite atlas presentation underlying the regular-`A_8` chart,
extract a finite list of canonical coefficient/multiplicity projections

```text
P_1,...,P_m
```

and finitely many fixed branch words whose compressed operators are partial
isometries `T_(j,i,h)` as in
`perron-frobenius-branching-carrier-collapse`.  Require the following uniform
properties for every sufficiently accurate trace-preserving finite-dimensional
atlas microstate after exactifying the fixed Pauli packet.

1. The branch incidence matrix `A=(a_ji)` has a fixed strongly connected
   component with Perron--Frobenius eigenvalue `rho>1`.
2. Incoming ranges at each target are pairwise orthogonal up to an error whose
   total normalized-HS mass is `O(delta^c)`.
3. The total off-target branch leakage in the Perron weights is

   ```text
   sum_j y_j e_j <= C delta^c.
   ```

4. The canonical regular-character constraints keep the Perron-weighted carrier
   mass bounded below:

   ```text
   sum_j y_j tau(P_j) >= c0 > 0.
   ```

The already established Pauli branch packet supplies the first genuinely
branching edge: two orthogonal isometric copies of the trace-`1/8` initial cut
`E` fill the trace-`1/4` transported carrier `F=U^*QU`.  Therefore a proof does
**not** need the old one-cut containment `F<=E`.  It is enough to find any fixed
finite low-leakage return path from `F` through other coefficient sectors back
to the strongly connected component containing `E`.  A cycle with one doubled
edge and otherwise single edges already has spectral radius `2^(1/L)>1`.

## Attempts

- **Immediate return `F -> E`.** This is the old support-containment theorem and
  remains sufficient, but it is unnecessarily strong.
- **Multi-chart return automaton.** Search the raw/comb/hard Pauli coefficient
  sectors as states and named compressor or middle-root words as edges.  Keep
  exact orthogonality data and measured leakage; any strongly connected
  component whose branch-count matrix has spectral radius above one is a valid
  certificate.
- **Transport-guided state selection.** Use the existing exact transport/Hall
  backend to propose low-leakage edges, but score a candidate by Perron radius
  rather than demanding a one-step Hall deficit.  This allows several
  individually trace-balanced transports to compose into a globally expanding
  cycle.
- **Falsification gate.** An exact finite atlas model carrying a positive-mass
  supercritical cycle would contradict the trace-capacity theorem immediately,
  so every candidate cycle should be checked against the exact coefficient
  audit before being promoted.