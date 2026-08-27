# Curvature-first audit of eight-cell Leavitt pictures

## Structural reduction

An eight-vertex trivalent spherical picture has twelve arcs and six regions,
with total face length 24.  In the strengthened short coefficient group

```text
Q=V_4(h_0,h_2) * V_4(k_0,k_1) * F(h_1,k_2),
```

every trivial word has even length.  If the five internal regions are
trivial in `Q`, the outer region is even as well.  The planar core is thus
bipartite, with four vertices in each color class.

This replaces the blind pairing space by `4 x 4` nonnegative matrices of
row and column sum three.  There are twelve types modulo independent row
and column permutations and only five connected planar types:

```text
0012/0111/1110/2100
0012/0111/1200/2010
0012/0120/1200/2001
0012/0210/1101/2010
0111/1011/1101/1110.
```

The last is the simple cube; the first four are its parallel-edge curvature
degenerations.  Their planar rotation systems number `8,8,8,8,1` up to
global reflection.  The possible face partitions are

```text
2,2,4,4,4,8       2,2,4,4,6,6
2,2,2,4,6,8       2,2,2,2,8,8
2,2,2,6,6,6       4,4,4,4,4,4.
```

## Label pruning

Orienting the twelve core edges determines whether each vertex has the
`++-` or `+--` relator orientation and locates its minority occurrence.
After immediate dipoles are removed, the two relator colors are assigned
and region labels reduced in `Q`.  Across all five cores and their rotations
there are 531804 compatible reduced maps.  None has five `Q`-trivial
regions, hence there is no eight-cell disk in this sector.

The nearest maps have four trivial regions.  The shortest remaining labels
are 36 oriented length-eight words.  Expanding the bridges

```text
h_1=q_0p_1,   k_2=p_0e_1
```

and applying the disjoint-root identities leaves a nonempty alternating
`G_0*G_1` normal form in every case.  A typical basic block is

```text
h_0h_1^(-1)h_2h_1=a_0p_1^(-1)e_0p_1.
```

Thus none of the shortest residual mixed words is an actual coefficient
identity.

## Boundary of the conclusion

The even-region short-atlas sector has picture area at least ten.  A putative
area-eight kernel must use a longer Leavitt coefficient identity not visible
in `Q`, early enough that the even-face/bipartite reduction no longer
applies.  This is a much smaller target than arbitrary eight-cell pictures,
but it is not yet a universal area-ten theorem.
