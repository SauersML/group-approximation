---
rg: 2
id: bounded-involutive-cayley-expanders-for-sl-n-two
kind: claim
title: The groups SL_n(2) admit bounded involutive Cayley expanders
distinct_from:
  dimension-expander-two-matching-square-function: that assumes linear maps expand subspace dimension; this supplies a genuine Hilbert-space Cayley gap and restricts every matching map to be an involution.
---

ESTABLISHED.  There are absolute constants `k` and `lambda>0` such that for
every `n>=3`, the group

```text
SL_n(2)=GL_n(2)
```

has a generating multiset `S_n` of at most `k` involutions satisfying the
unitary Poincare inequality `(IS1)` with gap `lambda`.

This is a formal consequence of two published uniform theorems.  Kassabov,
Lubotzky and Nikolov, *Finite Simple Groups as Expanders*, give bounded
generating sets with a uniform Cayley gap for all nonabelian finite simple
groups other than the Suzuki family.  Malcolm, *The Involution Width of
Finite Simple Groups*, proves that every element of a nonabelian finite
simple group is a product of at most four involutions.  The groups
`SL_n(2)` are center-free simple for `n>=3`.

Replace every generator in the first theorem by one factorization of length
at most four from the second.  The union of the factors has bounded size and
generates the same group.  If an old generator is `t_1...t_l`, `l<=4`, then

```text
||pi(t_1...t_l)v-v||^2 <=4 sum_j ||pi(t_j)v-v||^2.            (BIC1)
```

Averaging shows that the new involutive set has gap at least one sixteenth
of the old gap.  This supplies exactly the bounded perfect matchings needed
by the Schreier sampler; no unproved conversion from dimension expansion to
edge expansion is involved.
