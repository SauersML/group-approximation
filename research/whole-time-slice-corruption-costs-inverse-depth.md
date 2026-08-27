---
rg: 2
id: whole-time-slice-corruption-costs-inverse-depth
kind: claim
title: Erasing one whole time layer of a circuit Hamiltonian costs only an inverse-depth fraction
invalidates:
  - qpcp-rounder-from-adversarial-fault-tolerance
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
distinct_from:
  bgv-adversarial-fault-tolerance: that is the positive theorem, tolerating almost-linearly many corrupted qudits per time step; this is the counting fact about how little of a depth-D circuit Hamiltonian one whole time layer is, which is what makes that per-step guarantee inapplicable at constant energy density.
---

**ESTABLISHED.**  Let `H = (1/m) sum_a h_a` be a circuit Hamiltonian for a
depth-`D` circuit on `N` physical qudits, with `Theta(N)` terms attached to
each time layer and `m = Theta(N D)` terms in all.

Then the terms attached to any single time layer are a `Theta(1/D)` fraction
of all terms.  Consequently an adversary with a **constant** energy-density
budget `epsilon` can pay for the complete corruption of `Theta(epsilon D)`
whole time layers -- at least one as soon as `epsilon = Omega(1/D)` -- and
the resulting state is at energy density `O(1/D)`, which vanishes.

Per-timestep fault tolerance cannot repair this.  A scheme which tolerates
`f(N)` arbitrary corruptions at every time step is useless against an
adversary who overwrites **all** `N` physical qudits at one step whenever
`f(N) = o(N)`.  The strongest such theorem currently available,
`bgv-adversarial-fault-tolerance`, has

```text
f(N) = N / 2^(O(sqrt(log Nbar))) = N^(1-o(1)) = o(N),           (WTS1)
```

so it is on the wrong side of that threshold, by a subpolynomial and not a
constant factor.

This is a fence on the *division of labour*, not on fault tolerance.  It says
that making a catastrophic computation fault pay a **constant** fraction of
the constraints is combinatorial work which must be done by the amplifier --
`locality-preserving-constant-combinatorial-gap` -- before any exactification
argument is run.  It says nothing against combining the two.
