---
rg: 2
id: spherical-relation-quadruple-counts-proof
kind: route
title: One-colour binomial degrees plus deterministic factorization of relation degrees
target: spherical-relation-quadruple-counts
requires: []
---

For a fixed unitary `U_w` and fixed input point `x_i`, the indicators
`A_w(i,j)` for `j != i` are independent Bernoulli variables with success
probability exactly `p_d`, because `U_w x_i` is another unit vector and the
other cloud points are independent uniform points.  The diagonal term `j=i`
is one additional bounded summand, so every out-degree is a
`Bin(N-1,p_d)` variable plus a number in `{0,1}`.  The same statement holds
for an in-degree after conditioning on `x_j`, since for `i != j`

```text
||U_w x_i-x_j|| = ||x_i-U_w^*x_j||.
```

Choose, for example, an error `eps_d -> 0` and then choose `N(d)` so large
that

```text
N p_d eps_d^2 >> log N,
N p_d^3 -> infinity.
```

This is always possible for each `d`; no upper bound on the point-cloud size
is part of the construction.  Since these conditions also imply
`N p_d -> infinity`, the one diagonal summand is negligible.  Chernoff and a
union bound over the finitely many colours and the `2N` in/out vertices give,
with probability `1-o(1)`,

```text
d_w^out(i), d_w^in(i) = (1+O(eps_d)) N p_d
```

simultaneously for every `w,i`.

Now fix a relation `gh=k` and abbreviate `A=A_h`, `B=A_g`, `C=A_k`.  The
degree of an `i`-slot vertex factors as

```text
D_i = d_k^out(i) sum_j A(i,j) d_g^out(j),
```

so the uniform one-colour bounds give
`D_i=(1+O(eps_d))N^3p_d^3`.  Similarly

```text
D_j = d_g^out(j) sum_i A(i,j) d_k^out(i),
```

and the sum contains `d_h^in(j)` terms, giving the same estimate.  For an
`l`-slot vertex,

```text
D_l = sum_j B(j,l) sum_i A(i,j)d_k^out(i),
```

where each inner sum is `(1+O(eps_d))N^2p_d^2` and the outer sum has
`d_g^in(l)=(1+O(eps_d))Np_d` terms.  The `m`-slot formula is symmetric.
Hence every one-slot degree is `(1+o(1))N^3p_d^3`.

Finally, after fixing any two coloured slots in a four-partite edge, at most
two indices remain free.  Therefore **deterministically**, without any
probability estimate,

```text
codeg(v_1,v_2) <= N^2.
```

Fixing three or four slots gives the stronger bounds `N` and `1`.  Since
`N p_d^3 -> infinity`,

```text
N^2 / (N^3 p_d^3) = 1/(N p_d^3) -> 0,
```

so every repeated-slot codegree is negligible relative to a vertex degree.
The finite union over tested relations is harmless.
