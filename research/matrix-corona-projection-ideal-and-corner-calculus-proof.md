---
rg: 2
id: matrix-corona-projection-ideal-and-corner-calculus-proof
kind: route
title: Compress coordinatewise and translate finite ideal generation into rank domination
target: matrix-corona-projection-ideal-and-corner-calculus
requires:
  - matrix-corona-projection-monoid-is-rank-germs
---

Choose a coordinate projection lift `(p_n)`.  Compression sends a bounded
sequence `(x_n)` to `(p_nx_np_n)`.  Its range modulo norm-null sequences is
the entire corner, and its kernel is exactly the norm-null corner sequences.
After choosing bases of `ran(p_n)`, this gives `(CI1)`.

If `q` lies in `I(p)`, approximate `q` within norm less than one by a finite
sum

```text
sum_(j=1)^m x_j p y_j.
```

At every sufficiently late coordinate this sum has rank at most `m r_n` and
is less than one from the projection `q_n`.  Projection onto its range is
injective on `ran(q_n)`, so `s_n<=m r_n` eventually.  Conversely that rank
inequality gives `q <=_MvN p^(directSum m)` by the rank-germ comparison
theorem, hence `q in I(p)`.  This proves `(CI2)` and `(CI3)`.

Apply `(CI2)` to the unit projection, whose rank is `d_n`, to obtain `(CI4)`.
A full projection corner of a unital C-star algebra is strongly Morita
equivalent to the ambient algebra.

For `e_S,e_T`, all nonzero coordinate ranks equal one.  Eventual domination
by a fixed multiple is therefore exactly almost-inclusion of supports.  An
almost-disjoint family of infinite subsets of `N` of cardinality continuum
gives a continuum antichain, while all subsets modulo finite difference give
the stated order embedding.
