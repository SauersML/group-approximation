---
rg: 2
id: regular-bs14-cores-admit-dyadic-one-power-shadows
kind: claim
title: Regular BS14 cores admit dyadic one-power shadows at square-root level cost
distinct_from:
  bs14-long-cycles-admit-bounded-period-shadowing: that cuts every long packet into arbitrary lengths at most K and consequently needs the least common multiple of all 4^m-1; this uses the regular character to discard a slowly growing short spectrum and cuts the rest only into dyadic divisors of K, so the single power 4^K-1 suffices.
  bounded-cycle-level-has-only-polylogarithmic-error: that measures the universal least-common-multiple staircase; this gives a regular-branch, sequence-dependent shortcut whose quotient logarithm is linear rather than quadratic in K.
  fixed-level-bs14-compatible-basin: that isolates the remaining moving-basin comparison after a finite-period shadow; this improves the shadow/level scale but does not prove that the shadow enters the unknown basin.
---

Let `(R_n,S_n)` be exact finite-dimensional unitary representations of
`BS(1,4)`,

```text
R_n S_n R_n^(-1)=S_n^4,                               (DYS1)
```

and assume that the base generator has the regular limiting character,

```text
tr_(d_n)(S_n^a) -> 0             for every a !=0.     (DYS2)
```

There are powers of two `K_n -> infinity` and same-dimensional exact cores
`(R'_n,S'_n)` such that

```text
(S'_n)^(4^K_n-1)=1,                                  (DYS3)
||R_n-R'_n||_2^2 <= 12/K_n,
||S_n-S'_n||_2^2 <= (4+2pi^2/9)/K_n.                 (DYS4)
```

More quantitatively, for a fixed power of two `K=2^q`, let `mu_n(K)` be
the normalized dimension of the sum of the original fourth-power packets
of lengths at most

```text
L_K=K log_2 K=Kq.                                    (DYS5)
```

Then the shadow may be chosen with

```text
||R_n-R'_(n,K)||_2^2 <= 8/K+4mu_n(K),
||S_n-S'_(n,K)||_2^2 <= 2pi^2/(9K)+4mu_n(K),         (DYS6)
(S'_(n,K))^(4^K-1)=1.                                (DYS7)
```

For each fixed `K`, `(DYS2)` implies `mu_n(K)->0`.  A slow diagonal choice
of `K_n` makes `mu_n(K_n)<=1/K_n` and gives `(DYS3)--(DYS4)`.

The construction removes the least-common-multiple tax from the regular
branch.  Since the one-unipotent Iwahori quotient at level
`N=4^K-1` has order comparable to `N^3`, its logarithmic size is `Theta(K)`;
the shadow cost is therefore

```text
O((log |Q_(4^K-1)|)^(-1/2)).                         (DYS8)
```

This is a sequence-level preconditioner, not a uniform repair theorem for
one arbitrary tuple.  It leaves the decisive quantifier unchanged: the
unknown stability radius of the moving finite Iwahori quotient can still
shrink faster than `K^(-1/2)`.
