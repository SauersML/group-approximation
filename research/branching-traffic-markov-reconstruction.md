---
rg: 2
id: branching-traffic-markov-reconstruction
kind: claim
title: Near-canonical branching traffic laws reconstruct a multiplicative Markov table
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

**Target.** There is a finite/table-dependent quantitative reconstruction
principle: if a positive graph-indexed law on a finite group table satisfies
the permutation traffic identities on enough connected **branching** test
graphs to sufficiently small error, with the regular trace values on cycles,
then one can build a common-state-space family of doubly stochastic kernels
whose multiplication, inverse and trace defects are small.

This deliberately stops at Markov kernels rather than demanding permutations;
`markov-sofic-equals-sofic` supplies the final integrality for free. It also
uses traffic only at finite defect: `permutation-traffic-is-simultaneous-fixed-points`
already shows that at a normal `0/1` limit connected traffic values contain no
new asymptotic invariant beyond word membership.

## Attempts

- **Use cycles only.** Gives ordinary word traces and reconstructs no shared
  vertex/path consistency.
- **Assume every positive traffic functional is realizable by a finite action.**
  Far too strong; positivity is only a relaxation. The missing theorem must
  identify a finite set/hierarchy of branching identities that forces a
  Markov realization.
- **Search small branching graphs.** This remains the best falsification test:
  theta graphs, forks, diamonds and overlapping cycles can be optimized under
  unitary table constraints to look for a robust deviation from every Markov
  realization.
