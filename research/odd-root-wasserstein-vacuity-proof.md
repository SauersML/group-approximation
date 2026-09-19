---
rg: 2
id: odd-root-wasserstein-vacuity-proof
kind: route
title: Quantize any circle measure on a fine odd-root mesh
target: odd-root-wasserstein-target-is-vacuous
requires: []
---

The union of the root sets `mu_m` over odd `m` is dense in the unit circle.
Choose an odd `m` whose mesh is below `epsilon`, partition the circle into
Voronoi cells around `mu_m`, and move the mass of each cell to its centre.
The resulting measure is supported on odd-order roots and the transport moves
every point by less than `epsilon`, proving `(ORW1)`.  Applying the same
quantization to two equal marginals preserves their equality and still says
nothing about the relative eigenbases of the corresponding unitaries.
