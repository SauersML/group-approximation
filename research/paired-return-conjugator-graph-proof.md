---
rg: 2
id: paired-return-conjugator-graph-proof
kind: route
title: Synchronize the two graph lifts in a free stable-letter channel and descend through the amalgam normal form
target: paired-return-conjugator-graph-has-regular-mf-benign-witness
requires:
  - regular-mf-central-hnn-closure
artifacts:
  - notes/TRUE_PAIRED_RETURN_CENTRALIZER_SWITCH_CUTS_CONJUGATOR_GRAPH.md
---

Centralize the four-generated transition subgroup
`M=<alpha(K),beta(K)>` with two free stable letters.  The two graph lifts
`h |-> alpha(h)U_h` and `h |-> beta(h)U_h` have a common stable component.
The kernel of the resulting fold `K*K->K` says that their intersection with
`M` is the normal closure of the two basis differences.

Conjugating those differences by `alpha(K)` produces precisely the Cayley
edge words `gamma_(s q) gamma_q^-1`.  Cayley-path telescoping identifies the
normal closure with `<gamma_h gamma_1^-1:h in K>`, and the retraction killing
`a` proves this is exactly the graph's intersection with `M`.  The amalgam
normal form then forbids every unmatched stable word from returning to the
base.  This gives the exact five-generator cutter intersection.

The base is the residually finite group `F3 times F3`; two applications of
regular central-HNN closure supply the claimed regular operator-MF ambient.
