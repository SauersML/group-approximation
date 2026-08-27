---
rg: 2
id: atlas-unbounded-chart-width-proof
kind: route
title: Use the infinite Leavitt chart image and its locally finite coset graph
target: atlas-augmented-relations-have-unbounded-chart-width
requires:
  - atlas-charts-overlap-trivially
  - atlas-q14-augmented-zero-set-has-x30-one-escape
  - universal-leavitt-el4-nonsofic
  - atlas-q14-simple-overgroup-index-is-at-least-32
---

Every relator defining `Gamma_+` is a genuine kernel word for the canonical
two-chart map to the binary-Leavitt target `Q`.  Therefore there is a
surjection

```text
Gamma_+ ->> Q.                                       (UWP1)
```

The target is infinite.  Its two chart maps are faithful and their images
intersect trivially.  The same is therefore true of the two chart copies in
`Gamma_+`: a nontrivial intersection upstairs would map to a nontrivial chart
intersection downstairs.  In particular `Gamma_+` is infinite.

For fixed `k`, `(AB)^k` is a finite set of size at most
`|A|^k|B|^k`.  Hence it cannot equal the infinite group `Gamma_+`; this proves
`(UAW2)` directly.

For the graph `(UAW3)`, the edges incident at `gA` are indexed by `ga`,
`a in A`.  Two such edges have the same `B` endpoint exactly when their ratio
lies in `A intersect B=1`.  Thus the degree at every `A` vertex is `|A|`, and
similarly the degree at every `B` vertex is `|B|`; both equal 20160.  Since
`Q=<A,B>`, the graph is connected.  It has infinitely many edges and finite
degree, hence infinitely many vertices.  A connected locally finite graph of
finite diameter is finite, so its diameter is infinite.  Alternating chart
syllables are precisely edge walks in this incidence graph, which proves the
width interpretation.

In a finite quotient with intersection `T`, the same calculation changes the
degree to `[A:T]=[B:T]=d`; it gives `2[S:A]=2n` vertices.  A radius-`D` ball
in a degree-`d` graph has at most

```text
1+d sum_(j=0)^(D-1)(d-1)^j
```

vertices.  If the diameter is `D`, that ball covers the graph and yields
`(UAW6)`.  The earlier simple-overgroup sieve supplies the displayed values
of `d` in its first surviving intersection profiles.

Finally, the Bass--Serre interpretation makes the fence explicit.  Before
relations, the graph is the quotient of the `A8*A8` Bass--Serre tree.  A mixed
kernel word attaches a cycle in the chart-coset graph: the pair-cubes attach
six-step cycles, q14 a four-step cycle, and q19243 an eight-step cycle.  The
map `(UWP1)` proves that attaching all of these named cycle orbits still leaves
the infinite graph above.  Hence none of the named local cycles can furnish a
global diameter bound.
