---
rg: 2
id: split-decoder-cantor-fiber-proof
kind: route
title: Localize an idempotent defect and use output guards to pack decoder alternatives
target: split-decoders-have-generic-cantor-fibers
requires: []
artifacts:
  - research/artifacts/gottschalk-decoder-fibers-2026-09-07.md
  - research/artifacts/check-gottschalk-decoder-fibers-2026-09-07.py
  - research/artifacts/gottschalk-decoder-fibers-replay-2026-09-07.json
---

Sections 1-5 of the artifact give the full proof. A nontrivial local
retraction R=tau sigma changes a finite perturbation u of a constant
fixed point. Its image v=R(u) is a distinct finite perturbation with
sigma(u)=sigma(v), proving the pre-injective case.

For D={u!=v}, let H=D M^(-1) M and W=HN. Agreement of an output z
with sigma(u) on W makes its preferred preimage tau(z) agree with v
on H. Replacing v by u on D preserves all outputs of sigma; H contains
every read window that could be affected. Disjoint translates of W
allow independent replacements, including infinitely many at once.

The choice bits are read back at translated defect sites, so the resulting
map from binary product space into a single fiber is a continuous injection
with closed image. Infinite disjoint occurrences of the output guard form
a dense G_delta and a set of full Bernoulli measure. Orbit density also
forces infinitely many disjoint occurrences. These arguments prove the
topological and measure claims without finite-model assumptions.

This is a mathematical proof route; Cairn acceptance does not certify
the proof in a theorem-prover kernel.
