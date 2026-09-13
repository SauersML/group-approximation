---
rg: 2
id: f2-support-three-zero-divisors-need-support-at-least-22-proof
kind: route
title: Reduce a least counterexample to a labelled cubic graph with 20 vertices and exclude every labelling by exact sieves
target: f2-support-three-zero-divisors-need-support-at-least-22
requires:
  - small-non-up-left-support-has-no-orderable-quotient
---

Let `G` be torsion-free, and let `alpha, beta` be nonzero in `F_2[G]` with
`alpha beta = 0` and `|supp alpha| = 3`. Suppose `|supp beta| <= 21`.
Replace `beta` by a nonzero `beta'` with `alpha beta' = 0` whose support is
least, so that A--T's standing hypothesis in §2 of arXiv:1612.00934 holds.
Write `B = supp beta'` and `n = |B|`.

(1) **`n` is even.** Put `S = supp alpha * B`. For `s in S` and
`a in supp alpha`, at most one `b in B` has `a b = s`. So `s` has one, two or
three expressions `s = a b`, and its coefficient in `alpha beta'` is their
number mod 2. That coefficient is 0, so every `s` has exactly two
expressions. Counting pairs `(a, b)` gives `3 n = 2 |S|`.

(2) **`n = 20`.** A--T Cor 6.2 gives `n >= 20`, and `n <= 21` by assumption.
So `n = 20` by (1).

(3) **The graph.** The Kaplansky graph on `B` joins `b != b'` when
`a b = a' b'` for some `a, a' in supp alpha`. By (1) each `b` has exactly
three neighbours, counted with multiplicity. By A--T Thm 2.9, under the
standing hypothesis, the graph is connected, simple, cubic and
triangle-free. So it is isomorphic to one of the 97546 graphs of
`nauty-geng -c -t -d3 -D3 20`.

(4) **The labelling.** Left-multiply `alpha` by the inverse of one element
of its support, so `supp alpha = {1, x, y}`. The product is still 0 and `B`
is unchanged. Give the end at `b` of the edge from `a b = a' b'` the label
`a`. The two ends of an edge have different labels, since `a = a'` forces
`b = b'`. At each vertex the three ends carry `1, x, y`. Transport this
labelling to the geng graph along the isomorphism. The elements of `B`
give a map from the vertices into `G`, injective by construction, such that
every labelled edge holds in `G`.

(5) **Normalization.** Permuting `{1, x, y}` means left-multiplying `alpha`
by an inverse support element and renaming the generators. It preserves
everything in (4). So any one vertex may be assumed to carry `1, x, y` on
its edges in a fixed order.

(6) **Exclusion.** `zds3.c` extends labellings one vertex at a time from the
normalized vertex, and discards a partial or complete labelling only when a
sieve of §5 of the artifact fires. Each sieve derives, from the relations
the labelling reads, a contradiction in every torsion-free group with a
vertex-injective realization:
- Sieve 1 merges two cosets tagged by distinct elements of `S`, which would
  then be equal in `G`.
- Sieves 2 and 6 use that a torsion-free group has no `u != 1` with
  `u^e = 1` for `e >= 2`. They only add relators.
- Sieve 3 uses that a torsion-free group has no nontrivial finite
  subgroup, while the image of `<x, y>` contains `x != 1`.
- Sieve 5 is `small-non-up-left-support-has-no-orderable-quotient`.

A discarded labelling has no extension that is realized in any
torsion-free group. `n20.sbatch` runs every graph to the end of the search,
and no labelling survives. This contradicts (4), so `|supp beta| >= 22`.

**Evidence.** The program, the job scripts, the shard logs and the
per-graph GRAPH lines are listed in the claim. `agg.sh` checks that the
shards have 97546 graphs with no duplicates, exit codes 0, no survivors, and
no run that hits a limit.
