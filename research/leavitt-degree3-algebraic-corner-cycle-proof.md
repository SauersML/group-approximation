---
rg: 2
id: leavitt-degree3-algebraic-corner-cycle-proof
kind: route
title: Rewrite both unary corners and audit exact Leavitt collisions
target: leavitt-degree3-algebraic-corner-cycle-is-absent
requires:
  - leavitt-degree3-formal-corner-cycle-is-absent
  - leavitt-degree3-direct-pivot-screen-is-empty
---

For each of the eleven sign topologies and each of the `11!/4!=1,663,200`
placements of

```text
(r,e,a,c,1,b,d,p,1,1,1),
```

write the two unary corners as `H,Y`.  Pivoting gives `z=H^(-1)` and the
second unary relation gives `Y=H` (the unique stable-letter sign of both unary
orbits is positive).

The formal corner-core theorem says the nine-valent orbit has eight singleton
corners and one triple corner.  Unless that triple is exactly one of

```text
H, H^(-1), Y, Y^(-1),
```

the triple is globally singleton and the two-relator incidence peels.  The
artifact therefore computes those four equalities first in the faithful
twenty-leaf Bergman chart.  On an exact collision it rewrites `Y^+-1` as
`H^+-1`, substitutes every `z^+-1`, reduces in the free product of the three
coefficient copies, and cyclically reduces.  Cyclic reduction is essential:
it recognizes consequences of the form `H h H^(-1)=1`, not only the literal
word `h`.

MSI array job `16658576` completed all eleven shards with exit code zero.
Every shard reached offset `1650000` and its final `13200` layouts; no shard
printed `HIT`.  Thus the audit covers

```text
11 * 1,663,200 = 18,295,200
```

layouts.  Independent full runs of topologies zero, eight, and nine also
reported zero.  Equality is exact throughout; no finite quotient or hash is
used.
