---
rg: 2
id: brin-thompson-nekrashevych-wp-reduces-to-self-similar-group
kind: claim
title: The word problem of a finitely generated subgroup of a higher-dimensional Rover--Nekrashevych group nV_d(H) reduces to that of H with exponential rescaling
distinct_from:
  rover-nekrashevych-word-problem-reduces-to-self-similar-group: that is the one-dimensional group V_d(G); this is the product version nV_d(H), whose tables are bricks with an H-section in each coordinate, and which contains Brin's nV.
  complexity-bounded-host-classes-are-not-universal: that is the general non-universality principle; this is the upper bound that places the nV_d(H) family under it exactly when H ranges over a complexity-bounded class.
---

**ESTABLISHED** (elementary; no novelty claimed).

**Setting.**
- Let `d ≥ 2`, `X = {0,…,d-1}` and `n ≥ 1`. Let `H ≤ Aut(T_d)` be a finitely
  generated self-similar group with word problem decidable in non-decreasing
  time `T`.
- `nV_d(H)` is the group of homeomorphisms `f` of `(X^ω)^n` with a *decorated
  table*: two partitions of `(X^ω)^n` into bricks `Π_j C(u_{i,j})` and
  `Π_j C(v_{i,j})`, and elements `h_{i,j} ∈ H`, such that
  `f(u_{i,1} ζ_1, …, u_{i,n} ζ_n) = (v_{i,1} h_{i,1}(ζ_1), …, v_{i,n} h_{i,n}(ζ_n))`.
- For trivial `H` this is Brin's `nV`. For `n = 1` it is `V_d(H)`.

**Statement.** For every finitely generated `K ≤ nV_d(H)` and every finite
generating set of `K`, there is `c` such that the word problem of `K` is
decidable in time

```text
2^(c*l) * ( T(2^(c*l)) + 2^(c*l) ).                                  (BN1)
```

**Consequence.**
- **A fixed host.** `nV_d(H)` is complexity-bounded by `(BN1)`. So if `H`
  ranges over a class of self-similar groups sharing one recursive time bound,
  the hosts `nV_d(H)` form a class with one recursive bound. By
  `complexity-bounded-host-classes-are-not-universal`, that family is not
  universal.
- **The family.** The route of approach 1 of
  `research/artifacts/ideas-2026-09-13/bh/bh-contracting-selfsim.md` can only
  be universal if it uses self-similar `H` with arbitrarily hard word problems.
  The extra dimensions add no complexity of their own.

The proof is `brin-thompson-nekrashevych-wp-reduction-proof`.
