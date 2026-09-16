---
rg: 2
id: nucdim-factor-transfers-bounded-divisibility
kind: claim
title: A tensor factor of nuclear dimension at most m turns almost divisibility into divisibility up to the factor m+1
distinct_from:
  finite-elementary-tensor-blocks-are-divisible: that divides finite elementary tensor blocks for an arbitrary second factor with exact constants; this divides every Cuntz class of the tensor product, at the price of the bounded factor m+1, when the second factor has finite nuclear dimension.
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Let `A` be a C*-algebra whose Cuntz semigroup is almost divisible, and let `B`
be a C*-algebra with `dim_nuc B <= m` (separability is not needed).  Then for
every `a in ((A tensor_min B) tensor K)_+`, every `eps > 0` and every `N >= 1`
there is `Y in Cu(A tensor_min B)` with

```text
[(a-eps)_+] <= (N+1) Y          and          N Y <= (m+1) [a] .
```

Consequently, for every `N >= 1` and every `x' << x` in `Cu(A tensor_min B)`
there is `y` with

```text
x' << N y << 2(m+1) x ,
```

which is the divisibility hypothesis of Seth--Vilalta, arXiv:2602.14809v2,
Lemma 5.4 and Theorem 5.6, with constant `M = 2(m+1)`.
