# Area-ten structural audit for the three-gate Leavitt candidate

For ten trivalent vertices, `E=15`, `F=7`, and the face lengths total 30.
In the short coefficient atlas all internal identities are even, so the
outer face is even.  A digon-free map would have face partition

```text
4,4,4,4,4,4,6.
```

A digon-free cubic bipartite graph here would be simple, with a `5 x 5`
zero-one adjacency matrix of row/column sum three.  Its complement is a
2-regular bipartite graph on ten vertices, hence either `C_10` or
`C_4 disjoint_union C_6`.  Both complementary cubic graphs have a
`K_(3,3)` minor.  Hence neither is planar and a gate digon is forced.

Restoring one edge in all 33 planar rotations of the five bipartite
eight-vertex cores gives 396 rooted restorations and eleven face partitions:

```text
2,2,2,2,2,10,10   2,2,2,2,4,8,10
2,2,2,2,6,6,10    2,2,2,2,6,8,8
2,2,2,4,4,6,10    2,2,2,4,4,8,8
2,2,2,4,6,6,8     2,2,4,4,4,4,10
2,2,4,4,4,6,8     2,2,4,4,6,6,6
2,4,4,4,4,6,6.
```

The first type is a cycle of five digon gadgets with two global decagons.
The rooted pairing `(A10C1)` represents its unique ribbon type.  An exact
MSI audit over 3126 compatible edge orientations and all relator colorings
finds no way to make all five digons and one decagon trivial while leaving
the other decagon as boundary.  Thus the most economical candidate disk is
absent; ten less-degenerate partitions remain.
