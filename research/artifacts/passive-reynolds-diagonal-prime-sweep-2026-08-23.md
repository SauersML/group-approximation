# Passive Reynolds diagonal prime sweep

This is a numerical audit of the exact scalar column `(DSS3)` from
`constrained-reynolds-column-has-a-diagonal-scalar-shadow`; it is not used
as a proof.

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
```

For the five displayed primes where `<h(2)>` is the full projective split
torus, all nonzero singular values coincide and the scalar infinity inverse
stays below one in this normalization.  At `p=17` the torus index is two;
the tight-frame degeneracy splits and the infinity inverse increases, but
remains finite at this level.

The sweep rules out the simplest prediction that the actual arithmetic
column already behaves like the generic logarithmically bad cubic expander
at primitive prime levels.  It does not prove a uniform bound: the
load-bearing families are precisely those with unbounded torus index and
the composite/prime-power congruence rings, and the cb norm also requires
all matrix amplifications.

