---
rg: 2
id: qpcp-rounder-from-adversarial-fault-tolerance
kind: route
title: Round soft energy to faults using per-timestep adversarial fault tolerance
target: amplified-hamiltonian-has-a-constant-cost-rounder
requires: [bgv-adversarial-fault-tolerance]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Dead.**  Invalidated by
`whole-time-slice-corruption-costs-inverse-depth`.

The tempting argument.  Compile the circuit fault-tolerantly against
adversarial noise; a low-energy state of the circuit Hamiltonian is then a
noisy run of the compiled circuit; the fault-tolerance guarantee identifies a
correctable fault pattern; take that pattern as the set `S` and the corrected
run as `sigma_S`, with `|S|` proportional to the noise the state carries and
so to its energy.

Why it fails.  The strongest available guarantee,
`bgv-adversarial-fault-tolerance`, tolerates `N^(1-o(1)) = o(N)` corrupted
physical qudits **per time step**.  On a depth-`D` circuit Hamiltonian with
`Theta(N)` terms per layer and `Theta(N D)` terms in all, an adversary at
constant energy density can overwrite every one of the `N` qudits at a whole
layer while paying only a `Theta(1/D)` fraction of the constraints.  The
fault-tolerance hypothesis is then simply false at that layer, and the
argument has no correctable pattern to name.

The failure is one of division of labour and not of the theorem: making a
catastrophic temporal fault pay `Omega(m)` constraints is combinatorial work
belonging to `locality-preserving-constant-combinatorial-gap`.  Fault
tolerance is still needed downstream, for
`syndrome-conditioned-exactifier-exists`.
