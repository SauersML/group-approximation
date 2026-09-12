---
rg: 2
id: atlas-a8-t21-positive-word-cauchy-optimality-proof
kind: route
title: Exhaust the finite Cayley layers and finish by convexity of the count vector
target: atlas-a8-t21-positive-word-cauchy-optimality
requires: []
artifacts:
  - experiments/atlas_a8_t21_word_optimum.py
---

The exact dependency-free Cayley audit generates all `20160` elements of
`GL_4(F2)` from `T` and finds directed diameter `17`.  Its exact-length layers
show

```text
dist_T(1,t21)=8,
t21 is not reachable at exact length 9.
```

Exhausting all `4^8` length-eight positive words finds exactly four words for
`t21`, and every one has the same generator-count vector

```text
(2,0,2,4),
```

whose square-sum is `4+0+4+16=24`.

Any other positive word for `t21` therefore has length at least ten.  If four
nonnegative integer counts sum to `L>=10`, convexity of `x^2` shows that their
square-sum is minimized by distributing `L` as evenly as possible.  Already at
`L=10` this minimum is

```text
3^2+3^2+2^2+2^2=26>24,
```

and it increases thereafter.  Hence no longer positive word can beat the
length-eight coefficient `24`.

For a positive word `w`, repeated commutator telescoping gives

```text
d(t21) <= sum_t count_t(w) d(t),
```

and ordinary Cauchy gives the symmetric constant
`sum_t count_t(w)^2`.  The preceding finite argument therefore proves the
claimed global optimum within this proof architecture.