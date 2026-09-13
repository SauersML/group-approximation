---
rg: 2
id: branching-traffic-markov-reconstruction
kind: claim
title: Near-canonical branching traffic laws reconstruct a multiplicative Markov table
refuted_by:
  - cayley-traffic-law-refutes-markov-reconstruction
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
  - research/artifacts/q34-rounding-routes-2026-09-12.md
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
- **Refuted in its stated form** by
  `cayley-traffic-law-refutes-markov-reconstruction`.
  - The rooted Cayley law `lambda_G(T)` counts maps `V(T) -> G` with root
    value `e` and `phi(w) = l(e) phi(v)` on every edge.  For every group `G` it
    takes exactly the canonical permutation traffic values on every connected
    test graph, branching or not, with regular trace values on cycles.  It is
    reflection invariant, Gram positive and has nonnegative injective counts.
  - Feeding it to the principle gives Markov models of every window.  So the
    principle holds on the tables of `G` exactly when `G` is sofic
    (`markov-sofic-equals-sofic`), and it fails for the group of
    `finitely-presented-nonsofic-group-exists`.  No small-graph search is needed
    for this.
  - *Repair by restricting to hyperlinear ambient groups.*  The law never reads
    the microstate, so the restricted principle is Q3.4 itself.
  - *Repair by strengthening positivity* to every linear inequality valid on
    finite-action laws.  Reconstruction becomes trivial, and producing such a
    law from a microstate is per-window soficity.
  - A surviving reconstruction principle must take the microstate, not only its
    graph law, as input.
