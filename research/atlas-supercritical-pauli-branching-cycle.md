---
rg: 2
id: atlas-supercritical-pauli-branching-cycle
kind: claim
title: The atlas Pauli carriers contain a supercritical finite branching cycle
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - notes/TRUE_RAW_PAULI_COEFFICIENT_CUT.md
distinct_from:
  atlas-one-cut-finite-multiplicity-extraction: that forces one transported large carrier back under one smaller cut; this target permits the return path to wander through finitely many coefficient sectors and only asks that the resulting branching graph be supercritical.
---

For the fixed finite atlas presentation underlying the regular-`A_8` chart,
extract a finite list of canonical coefficient/multiplicity projections

```text
P_1,...,P_m
```

and finitely many fixed branch words whose compressed operators are partial
isometries `T_(j,i,h)`.  Let `A=(a_ji)` count branches from carrier `i` into
carrier `j`.  For each target `j` define

```text
l_j = sum_(i,h) ||(1-P_j) T_(j,i,h)||_2^2,
o_j = sum_((i,h)!=(i',h')) ||T_(j,i,h)^* T_(j,i',h')||_2^2.
```

Require the following uniform properties for every sufficiently accurate
trace-preserving finite-dimensional atlas microstate after exactifying the
fixed Pauli packet.

1. The branch incidence matrix has a fixed strongly connected component with
   Perron--Frobenius eigenvalue `rho>1`.
2. The combined wrong-target and nonorthogonality energy vanishes at a fixed
   power rate in the atlas defect:

   ```text
   sum_j y_j (2 l_j + o_j) <= C delta^c.
   ```

3. The canonical regular-character constraints keep the Perron-weighted carrier
   mass bounded below:

   ```text
   sum_j y_j tau(P_j) >= c0 > 0.
   ```

Here `y>0` is a fixed left Perron vector on the supercritical component.  It is
also enough to give a rational certificate `kappa>0`, `y>0` with
`A^T y >= (1+kappa)y`; the proof then uses `kappa` instead of `rho-1`.

The already established Pauli branch packet supplies the first genuinely
branching edge: two orthogonal isometric copies of the trace-`1/8` initial cut
`E` fill the trace-`1/4` transported carrier `F=U^*QU`.  Therefore a proof does
**not** need the old one-cut containment `F<=E`.  It is enough to find any fixed
finite low-energy return path from `F` through other coefficient sectors back
to the strongly connected component containing `E`.  A cycle with one doubled
edge and otherwise single edges already has spectral radius `2^(1/L)>1`.

## Attempts

- **Immediate return `F -> E`.** This is the old support-containment theorem and
  remains sufficient, but it is unnecessarily strong.
- **Multi-chart return automaton.** Search the raw/comb/hard Pauli coefficient
  sectors as states and named compressor or middle-root words as edges.  Track
  both off-target leakage and cross-branch Gram energy.  Any component with a
  rational positive subeigenvector certificate above one is enough; exact
  orthogonality is not required.
- **Transport-guided state selection.** Use the existing exact transport/Hall
  backend to propose low-leakage edges, but score a candidate by supercritical
  branch growth rather than demanding a one-step Hall deficit.  This allows
  several individually trace-balanced transports to compose into a globally
  expanding cycle.
- **Falsification gate.** An exact finite atlas model carrying a positive-mass
  supercritical cycle would contradict the Gram-capacity theorem immediately,
  so every candidate cycle should be checked against the exact coefficient
  audit before being promoted.