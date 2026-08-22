# Complete area-ten short-atlas census

The exact certificate is
`research/artifacts/search-leavitt-area-ten-short-atlas.py`.  It starts from
the five bipartite cubic area-eight adjacency cores and fixes one of the eight
local rotation bits, quotienting only simultaneous global reflection.  Of the
`5*2^7` trials, exactly 33 are planar rotations.  Restoring a two-vertex gate
digon on each of their twelve edges gives 396 rooted restorations and 276
distinct dart involutions.  Only exact dart-involution tuples are deduplicated.

For every restored map the certificate asserts:

* 30 darts form a fixed-point-free involution and a connected ten-vertex
  cubic graph;
* `phi(d)=rot(alpha(d))` has seven cycles, their lengths sum to 30, and their
  sorted lengths lie in the eleven-partition structural atlas;
* every one of the `2^15` edge directions is tested; a direction survives
  precisely when each vertex has a cyclic shift of `++-` or `+--`, which
  uniquely recovers relator orientation and occurrence indices;
* all `2^10` assignments of the two relator colors are tested after rejecting
  an immediate same-color inverse-occurrence dipole;
* each face word is read at the target dart corner and reduced in the exact
  free-product normal form

```text
Q = V4(h0,h2) * V4(k0,k1) * F(h1,k2).
```

In particular `k1` is involutive.  A disk is accepted if and only if exactly
six of the seven normal forms are empty and the seventh is nonempty.  Thus
every face, including a digon, is allowed to be the outer boundary.

The MSI census is:

```text
partition                 maps  orientations  admissible colors
2,2,2,2,2,10,10              8        25,008          1,487,456
2,2,2,2,4,8,10              28        80,584          5,263,440
2,2,2,2,6,6,10               8        22,704          1,438,432
2,2,2,2,6,8,8               52       147,160          9,537,008
2,2,2,4,4,6,10              36        95,224          6,420,912
2,2,2,4,4,8,8               16        42,464          2,904,256
2,2,2,4,6,6,8               84       220,056         14,833,136
2,2,4,4,4,4,10               8        19,632          1,270,368
2,2,4,4,4,6,8               16        39,264          2,695,360
2,2,4,4,6,6,6                8        19,632          1,442,400
2,4,4,4,4,6,6               12        26,280          1,583,952
TOTAL                       276       738,008         48,876,720
```

Every row has zero accepted disks.  Since the structural theorem contracts
an arbitrary forced digon and restores exactly this atlas, the census closes
the entire area-ten short-coefficient sector, not merely one selected ribbon
type or one choice of outer face.

The three exhaustive MSI invocations split the atlas by digon count:

```text
python3 research/artifacts/search-leavitt-area-ten-short-atlas.py --workers 16 --min-digons 4 --max-digons 5 --include-five-digon
python3 research/artifacts/search-leavitt-area-ten-short-atlas.py --workers 16 --min-digons 3 --max-digons 3
python3 research/artifacts/search-leavitt-area-ten-short-atlas.py --workers 16 --min-digons 1 --max-digons 2
```

The audited script has SHA-256
`d3a791fb716901faa10762a7082eb1ccc3f07fb6fc63f63455723b13e4c0c6da`.
