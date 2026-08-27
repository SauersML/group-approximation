---
rg: 2
id: constant-private-pauli-gadget-no-go-proof
kind: route
title: Extract a monochromatic logical rectangle and compare its repeated gadget piece
target: constant-private-pauli-gadgets-fail-incidence-separation
requires:
  - finite-offset-pauli-rectangles-violate-relative-gr-sixth
  - complete-pauli-rectangles-defeat-three-p-balance
---

For completeness, the finite-color rectangle step is elementary.  If the
edges of `K_(n,n)` have `r` colors, then for each right vertex some color
occurs on at least `n/r` incident edges.  Count triples consisting of a right
vertex, such a color, and a pair of left neighbors of that color.  There are
at least

```text
n binom(floor(n/r),2)
```

triples but only `r binom(n,2)` possible color/left-pair values.  For all
sufficiently large `n`, one value occurs for two right vertices, giving a
monochromatic `K_(2,2)`.

Traverse its four terminal paths alternately forward and backward, joining
their X terminals and Z terminals inside the appropriate equality clouds.
Contracting each nontrivial equality path gives at most four peripheral
syllables, hence `(CPG1)`.  Two forward traversals are distinct immersions of
the same labeled terminal path.  They give a piece of length `ell`.  The
one-sixth inequality fails for `ell>=2`; the established finite-offset result
handles `ell=1`.  Cancellation or a trivial peripheral gap only shortens the
contour and therefore fails the required reduced relative-girth condition
before one invokes Greendlinger.

For ordinary word balance, bounded subdivision changes the perimeter and the
largest two-pair interval by only `O(1)`.  The short-gap/diameter-gap rectangles
from the established complete-table theorem therefore retain ratio
`1-O(1/L)`, completing the second assertion.
