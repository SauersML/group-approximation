---
rg: 2
id: leavitt-d4-length12-rank8-nine-cyclic-classes-proof
kind: route
title: Canonicalize face chirality and the five-corner group-size word
target: leavitt-d4-length12-rank8-nine-cyclic-classes
requires: []
---

`research/artifacts/rank-degree4-length12-triangles.py` enumerates all 30
ordered cyclic contiguous partitions of the five-valent face, all six
cyclic/inverse orientations of each of the three triangle faces, and imposes
zero abelian projection for the coefficient boundary.  For the representative
`---+-+++++++` its exact rank census is

```text
rank 7: 6, rank 8: 42, rank 9: 108,
rank 10: 789, rank 11: 4035, rank 12: 1500.
```

Canonicalize a system by the normal/inverse chirality of its two
three-valent faces and its five-valent face, and by cyclically minimizing the
three pairs `(target token, grouped-corner count)` on the latter.  The 42
rank-eight systems split with multiplicities

```text
3, 9, 3, 6, 9, 3, 3, 3, 3,
```

hence exactly nine cyclic classes.  Their five-corner size words consist of
the three placements of `(1,1,3)`, together with one `(1,2,2)` class, across
the occurring chirality patterns.  This classification precedes possible
further identifications by global triangle reflection or carrier relabeling.

