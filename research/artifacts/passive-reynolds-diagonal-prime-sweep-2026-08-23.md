# Passive Reynolds diagonal prime sweep

This is a numerical audit of the exact scalar column `(DSS3)` from
`constrained-reynolds-column-has-a-diagonal-scalar-shadow`; it is not used
as a proof.  The reproducible implementations are
`experiments/passive_reynolds_index_probe.py` and
`experiments/passive_reynolds_projective_probe.py`.

For `Q=PSL_2(F_p)` in its left regular representation, the calculation
enumerated `Q`, formed the sign-induced basis for
`Ind_(<h(2),w>)^Q chi`, built the two unnormalized cubic sums in `(DSS3)`,
and computed their singular values and the ordinary infinity norm of the
Moore--Penrose inverse.  It ran on one MSI core with one BLAS thread.

```text
p   |Q|   |<h(2)>|  domain  rank  s_min     s_max     ||C^dagger||_inf
5    60       2        15     10   6.000000  6.000000   0.666667
7   168       3        28     21   6.928203  6.928203   0.750000
11  660       5        66     55   8.485281  8.485281   0.833333
13 1092       6        91     78   9.165151  9.165151   0.857143
17 2448       4       306    271   5.409378  8.873479   2.267430
19 3420       9       190    171  10.954451 10.954451   0.900000
31 14880      5      1488   1393   4.798107  9.974849   3.910501
43 39732      7      2838   2707   7.024467 11.744254   3.451840
```

The tall column need not be materialized in order to compute one absolute
row sum of its pseudoinverse.  Equivariance makes all input-coordinate row
sums equal up to sign, and

```text
(C^dagger)^T e_x = C (C^T C)^dagger e_x.
```

The implementation accumulates `C^T C` directly from its three-term rows.
For larger domains it applies the normal operator without forming it and
uses Landweber iteration; at `p=31` this agrees with the dense eigensolve to
eight displayed decimals.  This gives the additional one-core result

```text
p   |Q|      |<h(2)>|  torus index  domain  ||C^dagger||_inf
73  194472       9           4       10804       5.046199
```

For the five displayed primes where `<h(2)>` is the full projective split
torus, all nonzero singular values coincide and the scalar infinity inverse
stays below one in this normalization.  At `p=17` the torus index is two;
the tight-frame degeneracy splits and the infinity inverse increases, but
remains finite at this level.

The first unbounded-index data therefore move in the opposite direction
from the primitive tight frames: indices `2,3,4` already give norms about
`2.27, 3.45--3.91, 5.05`.  This is a falsification signal against a small
arithmetic constant, not a proof of divergence or even monotonicity.

## Right-Borel fixed slice

There is a much smaller exact reducing slice which tests whether the extra
torus label alone explains this growth.  Since `(DSS3)` is built from left
translations, it commutes with the right action of the upper Borel
subgroup `B`.  Its right-`B` fixed input consists of functions on
`P^1(F_p)=G/B` satisfying

```text
f(4z)=f(z),                 f(-1/z)=-f(z).
```

Restricting the same two cubic rows to this space gives matrices of size
only `2(p+1)` by approximately the torus index.  Direct pseudoinversion
gave

```text
p      torus index   input dim   rank   ||C_U^dagger||_inf
17          2            2         1          0.500000
31          3            4         3          1.000000
73          4            4         3          0.800000
127         9           10         9          1.495105
257        16           16        15          2.159231
683        31           32        31          2.023944
2113       48           48        47          2.409369
2731      105          106       105          2.794586
```

Thus the pure projective label slice grows much more slowly and does not
account for the full norms at `p=31,73`.  Any divergent mode, if it exists,
must use nontrivial right-`U` types or a subtler interaction among them.

This is **not** the whole right-`U` fixed space.  The latter carries the
right action of `T=B/U`, and the projective calculation is only its trivial
`T`-character block.  The exact decomposition and the dimension
`dim D^U=((p+1)/2)i_p` are proved in
`right-unipotent-reynolds-space-decomposes-into-torus-hecke-blocks`.

The sweep rules out the simplest prediction that the actual arithmetic
column already behaves like the generic logarithmically bad cubic expander
at primitive prime levels.  It does not prove a uniform bound: the
load-bearing families are precisely those with unbounded torus index and
the composite/prime-power congruence rings, and the cb norm also requires
all matrix amplifications.
