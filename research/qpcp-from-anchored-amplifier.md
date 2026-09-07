---
rg: 2
id: qpcp-from-anchored-amplifier
kind: route
title: Anchored amplifier plus constant-cost exactification gives a constant energy gap
target: quantum-pcp-constant-gap-local-hamiltonian
requires: [locality-preserving-constant-combinatorial-gap, amplifier-preserves-yes-energy-below-the-floor, amplified-hamiltonian-has-a-constant-cost-rounder, combinatorial-gap-and-rounder-give-energy-gap]
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

## Why sufficient

Criterion 7.1 of the attack, assembled. All three construction
prerequisites refer to one polynomial-time reduction and its uniform
constants; separate amplifiers cannot be substituted for each other.

The reduction of `locality-preserving-constant-combinatorial-gap` outputs a
constant-locality, constant-alphabet Hamiltonian `H'` whose NO instances have
combinatorial gap `beta > 0`.  By
`amplified-hamiltonian-has-a-constant-cost-rounder` those instances admit a
`C`-rounder with `C = O(1)`.  Apply the forward half of
`combinatorial-gap-and-rounder-give-energy-gap`:

```text
lambda_min(H'_NO) >= beta / C = Omega(1).
```

By `amplifier-preserves-yes-energy-below-the-floor` the YES side sits at
`lambda_min(H'_YES) <= a` with `beta/C-a >= epsilon > 0` uniformly.
The two sides are separated by an absolute constant, at constant locality and constant local
dimension, and the reduction is polynomial time from a QMA verifier.  That is
`quantum-pcp-constant-gap-local-hamiltonian`.

## What this route does and does not concede

It does **not** claim progress by itself. Conditional on the first
prerequisite, its third prerequisite is equivalent to the NO-side energy
floor, not to the entire target -- see the corrected converse in
`combinatorial-gap-and-rounder-give-energy-gap`.  The route is written so
that the equivalence is visible at the interface rather than hidden inside a
proof, and so that the genuinely new obligations are the ones reached through
`rounder-from-local-ports-and-exactifier`:
`amplifier-has-compatible-local-syndrome-effects`, which binds the ports
and exactifier to the same construction. This is a remaining obligation,
not a consequence of the two component claims being asserted separately.
