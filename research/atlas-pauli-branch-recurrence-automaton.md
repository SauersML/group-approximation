---
rg: 2
id: atlas-pauli-branch-recurrence-automaton
kind: claim
title: Both Pauli children recur through one finite low-energy coefficient automaton
artifacts:
  - notes/TRUE_PAULI_BRANCH_TRANSFER_PACKET.md
  - notes/TRUE_RAW_PAULI_COEFFICIENT_CUT.md
distinct_from:
  atlas-one-cut-finite-multiplicity-extraction: that asks the whole transported trace-1/4 carrier to leak into one trace-1/8 cut; this target allows the two trace-1/8 children to follow different finite coefficient routes and only asks for recurrent branch pressure with vanishing Gram overlap.
---

Use the exact two-child cell from `pauli-two-child-transfer-packet`, with
source `E` and orthogonal child ranges `R_0,R_1`.  Construct a fixed finite
family of additional canonical coefficient/multiplicity projections and fixed
word-derived partial isometries such that, in every sufficiently accurate
trace-preserving atlas microstate after exactifying the finite Pauli packet:

1. `E,R_0,R_1` are states of the family and the exact edges
   `E -> R_0`, `E -> R_1` are retained;
2. the directed multigraph on the retained states is strongly connected;
3. for each additional edge `i -> j`, its partial isometry has source exactly
   the state projection `P_i` and has total wrong-target leakage

   ```text
   ||(1-P_j)T||_2^2 = O(delta^c);
   ```

4. for every target, the ordered-pair Gram energy of distinct incoming branch
   ranges is `O(delta^c)` in total.

The state family and word menu are fixed independently of matrix dimension.
No spectral-radius estimate is part of this target.  Strong connectivity plus
the already-established genuine branch at `E` automatically gives a rational
supercritical certificate by
`strongly-connected-branching-gives-rational-pressure`.

## Attempts

- **Branch-specific return words.** Search for separate routes carrying `R_0`
  and `R_1` back toward `E`; they need not use the same compressor word or the
  same intermediate coefficient sectors.  The old one-cut containment forced
  both children through one support inequality and is substantially stronger.
- **Finite-state compiler search.** Treat exact Pauli/root-character cuts as
  states and short raw/comb/hard words as transition candidates.  Attach to
  each transition its exact symbolic source identity and its relator-controlled
  wrong-target/Gram energies.  Strongly connected components are then a graph
  search, and `experiments/branching_pf_certificate.py` checks the resulting
  branch pressure.
- **Avoid adjoint fake returns.** The formal adjoints `T_0^*,T_1^*` both return
  to `E`, but their incoming ranges coincide and hence have order-one Gram
  overlap.  `gram-branching-capacity-with-overlap` correctly charges this, so
  adjoints alone do not solve the target.
- **Use mixed words, not additive characters alone.** The exact character
  calculation in `TRUE_PAULI_BRANCH_TRANSFER_PACKET.md` shows that coefficient
  idempotent inclusion does not descend to additive-root spectral inclusion.
  Viable return edges must consume raw-compressor or cross-root multiplication
  information that can control actual coefficient-module support.