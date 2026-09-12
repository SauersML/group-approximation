---
rg: 2
id: principal-angle-transport-and-projection-frame-energy
kind: route
title: Move test projections by their principal angles and sum physical leakage before Cheeger
target: quantum-expansion-transports-across-leaking-corners
requires:
  - reflected-corners-control-defective-quantum-variance
artifacts:
  - research/artifacts/quantum-corner-expansion-transport-2026-09-08.md
---

For a projection `q`, the range projection of `pq` lies under `p`
and has rank at most that of `q`. Principal angles give trace loss
at most `tr(q(1-p))` and squared Hilbert--Schmidt displacement at
most twice that quantity. The energy seminorm has operator bound
`sqrt(2)`, so moving the test costs at most eight times its leakage
after squaring the triangle inequality. This yields the transferred
projection expansion and then the reflected-corner variance bound.

For a common tested corner, sum the leakage using the operator bound
on the cut sum. For a sequence of remaining corners, use symmetry
of `tr(p_j K(p_i))`: each unordered pair is charged exactly once,
so the pre-threshold total is half the seed boundary.

For a weighted projection frame `S`, write each Kraus commutator
with `q_i` as `[a,q_i]q_i+q_i[a,q_i]`. Operator row-column
Cauchy--Schwarz and `S<=C I` give the frame energy bound with
constant `4C`, independent of the number of projections.
