---
rg: 2
id: anchored-criterion-components-are-shift-satisfiable-proof
kind: route
title: Check the shifted standard reduction against each anchored-amplifier requirement, and shift a root witness for the converse
target: anchored-criterion-components-are-shift-satisfiable
requires: [positive-shift-trivializes-exact-combinatorial-soundness, kitaev-local-hamiltonian-is-qma-complete, combinatorial-gap-and-rounder-give-energy-gap]
artifacts:
  - research/artifacts/qpcp-positive-shift-audit-2026-09-11.md
---

## Why sufficient

The reduction of `kitaev-local-hamiltonian-is-qma-complete` has constant
locality, qubit dimension, polynomially many terms, and polynomial-bit
entries. By (PS1) the shifted reduction keeps all four.

Section 3 of the linked artifact takes each requirement in turn and exhibits
the witness: (PS2) for (LPC1); (PS3) or (PS5) for the cost clause; the trivial
ports and flags of (PS5) for compatible effects, port domination and the
exactifier; the resolution `T_[m]=I` for the kernel-resolution clauses. The
term-wise bound `h'_a>=epsilon I` gives the anchor and recursion inequalities
for any partition of the terms into layers.

The YES computation is (PS4). The converse uses (PS2), (PS4), and identity
(CR4) of `combinatorial-gap-and-rounder-give-energy-gap`: every NO output of
the shifted witness has least rounder constant at most
`1/((1-epsilon)b*+epsilon)`, which is uniform because `b*` is a constant.
