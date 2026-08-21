---
rg: 2
id: short-gap-long-gap-pauli-rectangle-proof
kind: route
title: Put one cloud edge and one cloud diameter in the same complete-table rectangle
target: complete-pauli-rectangles-defeat-three-p-balance
requires: []
---

Fix an X-cloud equality edge joining the `r` and `s` pair-test occurrences.
Because the table tests every row-column pair, any choice of a second row
`q'` completes those two ports to a rectangle.  Choose `q'` farthest from
`q` in the Z cloud for `r`.  One gap is one and another is the diameter `L`.

Write the cyclic gaps as `a,b,c,d` and take `a=min(a,b,c,d)`.  Starting just
after the pair edge preceding `a` and ending just before the pair edge
following `a`, in the complementary direction, gives a cyclic interval
which contains the other three gaps and only the other two pair edges.
After moving the endpoints by a bounded amount inside the adjacent edges,
its length is at least `T-a-O(1)`.  Since `a<=1` and `T>=L`, its fraction is
`1-O(1/L)`.  This proves `(CPB1)`.

