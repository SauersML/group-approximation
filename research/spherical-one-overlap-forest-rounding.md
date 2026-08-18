---
rg: 2
id: spherical-one-overlap-forest-rounding
kind: claim
title: Regular-character unitary tables with a one-overlap relation forest round to partial Schreier tables
distinct_from:
  hypergraph-near-perfect-schreier-packing: This closes the packing problem only when the relation-incidence system is acyclic in the explicit one-overlap ordering below; the global node must synchronize cycles where a new relation reuses two or three previously chosen label maps.
---

Let a fixed finite partial multiplication table have finitely many labels and
relations `gh=k`.  Suppose its relations can be ordered componentwise so that

- the first relation of each component introduces all of its labels; and
- every later relation meets the set of labels seen earlier in **exactly one**
  label and introduces its other two labels.

Then every regular-character normalized-HS unitary model of this table with
defect tending to zero admits partial permutation models on finite sets such
that

- every label map is a bijection between subsets missing `o(N)` points;
- every listed multiplication relation holds exactly on `1-o(1)` roots; and
- distinct table labels disagree on `1-o(1)` roots.

Completing the partial bijections arbitrarily therefore gives permutation
models with vanishing Hamming multiplication error and the required regular
separation.

So Q3.4 has no obstruction on one-overlap relation forests.  In the spherical
packing route, the first genuinely new combinatorial content is **cycle
synchronization**: a relation which reuses at least two maps already fixed by
other relations.
