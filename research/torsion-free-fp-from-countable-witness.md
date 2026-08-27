---
rg: 2
id: torsion-free-fp-from-countable-witness
kind: route
title: Embed a torsion-free countable non-MF group into a finitely presented one
target: torsion-free-finitely-presented-non-mf
requires: [torsion-free-countable-non-mf, torsion-free-higman-embedding, mf-positive-controls]
---

## Why sufficient

Let `K` be a torsion-free recursively presented non-MF group and let
`K <= G` with `G` finitely presented and torsion-free.  If `G` were MF then
`K` would be MF, because subgroups of MF groups are MF
(`mf-positive-controls`: restrict an injective corona representation).  So
`G` is not MF, and `G` is torsion-free and finitely presented.

The value of this route is that it removes finite presentation from the
target of any new mechanism: a construction may use an infinite
presentation, a direct limit, or an infinitely presented small-cancellation
quotient, provided it stays recursively presented and torsion-free.  Its
cost is that it inherits the unverified status of
`torsion-free-higman-embedding`.
