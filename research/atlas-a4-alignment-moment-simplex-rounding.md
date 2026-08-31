---
rg: 2
id: atlas-a4-alignment-moment-simplex-rounding
kind: claim
title: The exact regular A4 network rounds on thirty-one moments to the classical alignment simplex
distinct_from:
  atlas-a4-relative-packet-commutator-collapse: packet collapse rounds the relative chart unitary itself into the global A8 commutant; this claim asks only for thirty-one scalar trace moments to lie asymptotically in the convex hull of all inner and outer chart alignments.
  atlas-a4-holonomy-coherence-gap: the holonomy gap asks for a numerical two-generator covariance ceiling; this claim is a weaker trace-level rounding interface from which the new classical separator already gives a contradiction.
artifacts:
  - experiments/atlas_triangle_19243_classical_gap.py
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Let `sigma_n` satisfy the exact-regular normalized A4 context-network hypotheses
of `atlas-a4-holonomy-coherence-gap`.  Choose arbitrary regular frames for the
two A8 chart vertices and let `tau_n` be normalized matrix trace applied to
words in the resulting two chart representations.

Write `w_1,...,w_30` for the thirty shortest pair-cubes and `q=q_19243` for the
collision word.  Prove that there are probability distributions `nu_n` on the
finite set

```text
Aut(A8) = (inner alignments) union (outer alignments)
```

such that, with `tau_(nu_n)` the corresponding convex mixture of regular
alignment trace states,

```text
max_(u in {w_1,...,w_30,q})
  |tau_n(u)-tau_(nu_n)(u)| -> 0.                       (A4-MOMENT-ROUND)
```

This is deliberately only a **finite moment rounding theorem**.  It does not
ask for a decomposition of the Hilbert space into alignment sectors, for a
normalizer approximation to the relative chart unitary, or for packet
commutators to vanish.  Those are all stronger than what the one-fifth
classical collision audit needs.

## Attempts

- **Qutrit-wire moment rounding.**  Use
  `a4-coherence-fan-canonically-splits-multiplicity` to push every local A4
  context to one fixed three-state tensor and one multiplicity wire.  Instead
  of synchronizing the wires in operator norm, average their cycle data only
  against the thirty-one word observables.  The target is a probability law on
  the finite automorphism alphabet, not one common gauge.
- **Connection-Laplacian dephasing.**  After quotienting a spanning-tree gauge,
  the context compiler has finitely many unitary cycle variables.  Seek a
  pinching/conditional-expectation argument showing that off-diagonal
  coherence between inequivalent automorphism sectors cannot affect the chosen
  word traces without paying one of the exact A4 loop residuals.
- **Finite tracial SOS.**  The conclusion only concerns a fixed vector in
  `C^31`.  Build the convex hull of the `40320` exact alignment profiles and
  search for separating hyperplanes against feasible truncated tracial moment
  matrices of the A4 network.  A low-degree cyclic sum-of-squares certificate
  would prove exactly the needed statement without reconstructing any chart
  unitary.
- **Do not over-solve the packet-centrality problem.**  The new
  `atlas-a4-classical-mixture-trace-separator` already survives arbitrary
  convex mixtures.  A proof that selects one alignment, or even an operator
  direct sum of alignments, contains unnecessary information.
