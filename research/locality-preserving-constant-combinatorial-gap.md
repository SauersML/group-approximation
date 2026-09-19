---
rg: 2
id: locality-preserving-constant-combinatorial-gap
kind: claim
title: A locality-preserving amplifier delivers a constant combinatorial gap at constant alphabet
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

Criterion (C) of the attack.  There is a polynomial-time reduction from a QMA
verifier to a Hamiltonian `H' = (1/m) sum_a h'_a` of **constant** locality and
**constant** local dimension such that in every NO instance the combinatorial
gap is a universal constant:

```text
every normalized sigma exactly satisfying all terms outside S
has |S| >= beta m,        beta > 0 absolute.                    (LPC1)
```

"Exactly satisfying" is `Tr(h'_a sigma) = 0`, equivalently `h'_a sigma = 0`.

**Status of the announced amplifier.**  The Simons Institute talk *Gap
Amplification for Local Hamiltonians with Combinatorial Soundness* (Quynh T.
Nguyen, Harvard, 23 July 2026, Quantum Summer Cluster Final Workshop)
announces "the first known viable template for quantum locality-preserving
gap amplification" and states "we prove that our procedure amplifies
combinatorial gap".  This claim is **not** established by that citation, for
two reasons recorded in
`research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md`:

1. no preprint carrying checkable hypotheses and parameters was locatable on
   2026-08-25, and an incoming attribution to three authors could not be
   confirmed against the Simons page, which names only the speaker;
2. even at face value the abstract announces *amplification* of the
   combinatorial gap while "moderately increasing its local qudit dimension".
   Driving an inverse-polynomial gap to a constant needs `Theta(log)`
   iterations, and nothing quoted bounds the alphabet after iteration.
   (LPC1) asks for constant gap **and** constant alphabet simultaneously.

Update this node, do not weaken it, when the preprint appears.

## Attempts

- **Ordinary energy amplification then reinterpretation.**  Fails before it
  begins: `ordinary-gap-amplification-grows-locality` spends exactly the
  constant-locality promise (LPC1) is stated at.
- **Read the constant gap off adversarial fault tolerance.**  Fails by
  `whole-time-slice-corruption-costs-inverse-depth`: making a catastrophic
  computation fault cost a constant fraction of constraints is the work
  (LPC1) has to do, and per-timestep tolerance of `o(N)` corruptions does not
  do it.
- **Take the talk as a citation.**  Declined above; the missing quantity is
  the alphabet after the iteration to constant gap.
