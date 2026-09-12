---
rg: 2
id: random-complex-cocycle-cheeger-beats-triangle-count
kind: claim
title: In the mid-range the permutation cocycle Cheeger constant beats the inverse triangle count
refuted_by:
  - random-complex-cheeger-capped-by-triangle-count
distinct_from:
  random-complex-linear-cocycle-stability: that asks the cocycle Cheeger constant to be bounded away from zero; this asks only that it beat the inverse triangle count n^(-2-η), which is exactly what Chapman--Peled Theorem 1.1 assumes
  finite-quotient-caps-cocycle-cheeger-constant: that is a proved deterministic upper bound at one pair of complexes; this is the open probabilistic lower bound, which that cap would contradict at any complex whose group detects a random missing triangle in a finite quotient
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

**OPEN, conjectural.** For some `0 < η < 1/2`, with `p = n^(-1+η)` and
`Y ~ Y(n,p)`, a.a.s.

```text
h_1(Y, Sym) = ω(n^(-3) p^(-1)) = ω(n^(-2-η)).                    (CPT)
```

This is the hypothesis of Chapman--Peled Theorem 1.1 verbatim. The older node
`random-complex-linear-cocycle-stability` asks for a constant lower bound, which
is strictly stronger (`random-complex-cheeger-threshold-from-linear-rate`).

## What any proof must contain

By `finite-quotient-caps-cocycle-cheeger-constant`, (CPT) forces the following:
a.a.s., for a random triangle added to `Y`, its perimeter lies in the finite
residual of `π_1(Y)` while remaining nontrivial there. So (CPT) already produces
a non-residually-finite hyperbolic group (`non-rf-hyperbolic-via-cheeger-threshold`).

A proof of (CPT) is therefore a proof about the finite quotients of random
Kazhdan hyperbolic groups, not a free-standing probability lemma. By
Meshulam's theorem (`meshulam-random-complex-no-polynomial-quotients`), the
quotients it must control are larger than every polynomial in `n`.

Conversely, residual finiteness of these random groups refutes (CPT) outright,
through `random-complex-cheeger-capped-via-detecting-quotient`.
