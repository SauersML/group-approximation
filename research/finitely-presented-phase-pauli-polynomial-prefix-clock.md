---
rg: 2
id: finitely-presented-phase-pauli-polynomial-prefix-clock
kind: claim
title: One finite presentation realizes the phase-Pauli polynomial clock and preserves pulse prefixes
distinct_from:
  cyclic-phase-pauli-shears-have-unbounded-clock-order: that supplies compatible finite clocks and their exact phase lifts; this asks for one finitely presented universal group with quantitative derived-word control.
  packet-hard-transport-preserves-pulse-prefix: that states the analytic prefix-leakage estimate needed by the Fanizza route; this is a proposed algebraic source for it.
---

Construct a finitely presented group containing a ring-valued phase-Heisenberg
subgroup and two involutive clock words whose finite cyclic quotients induce
the automorphisms in `(CPC3)`.  It must also contain level-local packet
transport words `V_n` such that

```text
V_n B_k V_n^-1=B_k                 for every k<n,               (FPP1)
```

while the current forbidden hard sign is sent to `B_n`.  All level-`n`
identities must have polynomial derivation area from the fixed presentation.

Equation `(FPP1)` makes the prefix leakage in `(PCF3)` polynomially bounded
and hence supplies `packet-hard-transport-preserves-pulse-prefix`.  The
cyclic models prove that the desired clock and its quadratic phase correction
are mutually consistent at every finite depth.  They do not prove finite
presentability, nor do they yet produce the level-local centralizer in
`(FPP1)`.

## Attempts

- The abstract semidirect product of the Laurent phase-Pauli module by the two
  shears has the correct finite quotients, but its evident presentation has
  infinitely many phase-root and distant-commutator relations.
- Embedding the clock in a high-rank Steinberg or Jacobi group should make the
  linear syntax finite.  The unresolved point is a ring-valued fourth-root
  center compatible with the Boolean involution packets and with the local
  centralizers in `(FPP1)`.
