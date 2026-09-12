---
rg: 2
id: weighted-hall-interdiction-formula
kind: claim
title: The cheapest support deletion creating a weighted Hall deficit is an explicit cut-interdiction minimum
artifacts:
  - experiments/weighted_hall_interdiction.py
  - experiments/weighted-hall-interdiction-smoke.json
  - experiments/weighted-hall-interdiction-smoke.out.json
---

Let `G=(L,R,E)` be a finite bipartite graph with nonnegative rational vertex
weights `alpha_i` on `L`, `beta_j` on `R`, and nonnegative edge deletion costs
`c_(i,j)`.  For `F subset E`, write `G-F` for the graph after deleting `F`.
The minimum cost of an edge set whose deletion creates a strict weighted Hall
deficit is

```text
min {
  sum_(i in S, j notin T, (i,j) in E) c_(i,j) :
  S subset L,
  T subset R,
  sum_(i in S) alpha_i > sum_(j in T) beta_j
}.                                                       (WHI1)
```

A minimizing pair `(S,T)` gives an explicit optimal deletion set

```text
F_(S,T) = E intersect (S x (R\T)).                     (WHI2)
```

After deleting it, every remaining neighbor of `S` lies in `T`, so the Hall
deficit is at least `alpha(S)-beta(T)>0`.

Conversely, every deletion set `F` that makes `G-F` Hall-deficient contains
`F_(S,N_(G-F)(S))` for some deficient `S`, so its cost is at least the value
of `(WHI1)`.

For the atlas Fourier search this reverses the expensive loop.  Given any
baseline block-support graph and a cost assigned to proving each block small
(for example degree, certificate size, or an empirical difficulty score), one
can first solve `(WHI1)` and then target only the cheapest relation-sensitive
block family capable of creating a deficit.
