# Forced-digon contraction closes the long odd area-eight residue

The remaining face partitions were

```text
2,2,2,2,5,11       2,2,2,3,4,11
1,2,2,2,6,11       1,2,2,4,4,11
2,2,2,2,3,13       1,2,2,2,4,13
1,2,2,2,2,15.
```

Every internal 2-face is one of the four gate squares.  Such digons are
vertex-disjoint in a connected eight-vertex cubic graph.  Contracting one
deletes two vertices and subtracts two from each adjacent nondigon face.

After two contractions the core has four cubic vertices and its face
partition must be one of

```text
1,1,5,5   1,1,2,8   1,1,1,9
1,2,3,6   2,2,4,4   3,3,3,3.
```

After three contractions the two-vertex core is either `1,1,4` or `2,2,2`.
After four, the terminal connected object is one vertexless circle, and
re-expansion produces global faces `8,8`.

For each target partition, distribute the two face incidences of every
digon among the nondigon faces and subtract two per incidence.  None matches
an allowed core partition.  The exact MSI certificate prints

```text
(2,2,2,2,5,11) MATCHES []
(2,2,2,3,4,11) MATCHES []
(1,2,2,2,6,11) MATCHES []
(1,2,2,4,4,11) MATCHES []
(2,2,2,2,3,13) MATCHES []
(1,2,2,2,4,13) MATCHES []
(1,2,2,2,2,15) MATCHES []
```

Hence no long-odd area-eight core exists.  The area-eight residue is empty
before any further Leavitt root identity can enter.
