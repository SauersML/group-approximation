---
rg: 2
id: zn-rips-sphere-balanced-dominator-criterion
kind: claim
title: The Rips complex of Z^n at scale r is contractible when every partition of r into at most n parts has a balanced sub-vector
distinct_from:
  z6-rips-contractible-at-scales-6-to-9: that is a per-scale computer certificate on the whole peeling-link set Lmax (about |Lmax| moves); this is a scale-free criterion that only looks at integer partitions of r, so it can be checked at scales where Lmax has 10^8 or more points
  zaremsky-rips-contractibility-criterion: that criterion needs small enclosing balls with a central centre for every diameter above the scale; this one is a statement about the top sphere |x|_1 = r only
---

Call a vector `x ∈ Z_{≥1}^s` **balanced** if there is an integer vector `y` with `0 ≤ y ≤ x`, `y ≠ 0`, `y ≠ x`,
such that for every sign vector `σ ∈ {±1}^s` the number `⟨σ, y⟩` lies in the closed interval between `0` and
`⟨σ, x⟩`. (Equivalently, there is no split `J ⊔ J^c` of the coordinates with `y(J) > y(J^c)` and
`w(J) < w(J^c)`, where `w = x − y`.)

**Theorem.** Let `n ≥ 1` and `r ≥ 2`. If every partition of `r` into at most `n` positive parts, read as a
vector, is balanced, then `VR(Z^n, d_1; r)` is contractible.

The hypothesis is a finite check over integer partitions and does not grow with the lattice. The route
`zn-rips-sphere-balanced-dominator-criterion-proof` proves the theorem. Its core is a domination lemma:
a balanced `y ∈ hull(0,x)` is within `r` of every `z` with `|z|_1 ≤ r` and `d_1(z,x) ≤ r`. With it, every point of
the top sphere `|x|_1 = r` of each peeling link can be deleted, and then the rest of the link collapses onto
`e_k`, one norm at a time.

Computed status of the hypothesis (`experiments/zn-rips-sphere-core-2026-09-17/results.txt`). A partition with
`s` parts is unbalanced only when its sum is
- `s ≤ 2`: `s`;
- `s = 3`: `3`;
- `s = 4`: `4, 5`;
- `s = 5`: `5, 6, 7, 9`;
- `s = 6`: `6, …, 11, 13, 15, 17`;
- `s = 7`: `7, …, 19, 21, 23, …, 35`.

All sums up to 54 were checked. So the criterion proves contractibility for these `(n, r)` with `r ≤ 54`
(above `n(n+1) − 1`, Zaremsky's published bound already applies):
- `n = 3`: `r ≥ 4`;
- `n = 4`: `r ≥ 6`;
- `n = 5`: `r = 8` and `10 ≤ r ≤ 54`;
- `n = 6`: `r ∈ {12, 14, 16}` and `18 ≤ r ≤ 54`;
- `n = 7`: even `r` with `20 ≤ r ≤ 34`, and every `r` with `36 ≤ r ≤ 54`.

For `n = 7` this is new: `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54`. The known
non-contractible scale `r = n − 1` is correctly excluded, since `(1,…,1)` is unbalanced. The criterion is
not sharp: the scales `n ≤ r < T(n)` it misses include many known contractible ones.
