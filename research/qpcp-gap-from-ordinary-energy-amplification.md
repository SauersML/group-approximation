---
rg: 2
id: qpcp-gap-from-ordinary-energy-amplification
kind: route
title: Amplify the ordinary energy gap to a constant with the detectability lemma
target: quantum-pcp-constant-gap-local-hamiltonian
requires: []
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
---

**Dead.**  Invalidated by `ordinary-gap-amplification-grows-locality`.

The tempting argument.  QMA-hardness of the local Hamiltonian problem is
known at inverse-polynomial gap.  Aharonov--Arad--Landau--Vazirani amplify the
gap of a local Hamiltonian on an expander interaction graph.  Iterate until
the gap is constant.

Why it fails.  The amplification reads a `t`-step neighbourhood of the
interaction graph as a single constraint, so the locality of the output grows
with the amplification parameter, and driving an inverse-polynomial gap to a
constant drives the locality to `omega(1)`.  The conjecture at
`quantum-pcp-constant-gap-local-hamiltonian` fixes the locality at a constant
`k`, so the iterated construction has spent exactly the promise it was meant
to preserve.  The July 2026 Simons abstract describes locality-preserving
amplification as still without a known quantum analogue at that date, and
offers the first template for one.

This is why the attack targets the **combinatorial** gap instead: an
amplifier which preserves locality while increasing only the local dimension
keeps `k` fixed, and the conversion back to ordinary energy is then the
exactification problem rather than another amplification.
