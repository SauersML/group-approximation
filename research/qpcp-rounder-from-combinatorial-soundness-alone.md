---
rg: 2
id: qpcp-rounder-from-combinatorial-soundness-alone
kind: route
title: Extract a rounder from combinatorial soundness and local energy accounting alone
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [locality-preserving-constant-combinatorial-gap]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
---

**Dead.** Invalidated by
`qubit-pairs-have-half-gap-and-unbounded-rounder-cost`.

The tempting argument.  Combinatorial soundness already says that exact
satisfaction off `S` forces `|S| >= beta m`.  A state of small energy
violates few constraints "on average", so round each violated constraint to a
fault, count the faults, and the count should be `O(energy)`.

Why it fails. The explicit rational one-qubit projector pairs of that claim
give `2N` terms on `N` qubits with combinatorial gap `1/2`, occurrence two,
and normalized ground energy `1/(N^2+1)`. Every exactification of every
input has at least `N` faults, so a ground input forces
`C >= (N^2+1)/2`. Constant preparation attains this bound. No locality,
efficiency, or faithfulness restriction on the rounder is used.

The earlier shear argument required endpoint faithfulness and had zero
combinatorial gap, so it did not by itself refute the implication stated
here. The new example supplies both missing qualifications. It refutes the
generic inference from combinatorial soundness and incidence alone, not the
possibility of an amplifier with additional useful structure. Constructing
that structure remains the task of
`local-syndrome-port-domination-at-each-gadget` and
`syndrome-conditioned-exactifier-exists`.
