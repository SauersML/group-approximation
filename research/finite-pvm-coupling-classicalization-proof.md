---
rg: 2
id: finite-pvm-coupling-classicalization-proof
kind: route
title: Use compactness and nonnegative inverses to force monomial stochastic matrices
target: finite-pvm-couplings-with-approximate-inverses-classicalize
requires: []
---

Divide the `j`th column of a coupling `C` by `mu_j`.  This identifies
self-couplings of `mu` with `mu`-stationary Markov matrices, and `(FPC2)`
with ordinary matrix multiplication.  The set of such matrices is compact,
uniformly for probability vectors with nonzero entries at least `c`.

If the conclusion failed, take a sequence with `epsilon_n->0` and pass to a
subsequence on which `mu_n` and every tested Markov matrix converge.  The
limits satisfy the multiplication table exactly.  In particular the limits
for `g` and `g^(-1)` are inverse nonnegative matrices.

An invertible nonnegative matrix whose inverse is nonnegative is monomial.
Indeed, from

```text
0=(AB)_(i,k)=sum_j A_(i,j)B_(j,k)       (i!=k)
```

every nonzero entry in row `i` of `A` forces the corresponding row of `B`
to be supported only at `i`.  Invertibility then forces exactly one nonzero
entry in every row and column.  Stochasticity makes those entries one, and
stationarity makes the resulting permutation preserve `mu`.

The exact limit multiplication table therefore consists of
`mu`-preserving permutations.  Compactness gives the asserted uniform
modulus, and continuity of multiplication gives approximate
multiplicativity of nearest permutations.  Approximate `mu` by rational
weights, split each atom into its numerator number of points, and replicate
all atoms by a common denominator.  A `mu`-preserving atom permutation then
lifts to an ordinary permutation of the replicated finite set.  The weight
and coupling errors become normalized Hamming errors.  This proves the
claim.

