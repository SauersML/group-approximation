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

## Attempts

1. **Known-sofic regimes (2026-09-13): no kill.** Chapman--Peled's positive
   results sit outside the range of (CPT): Theorem 1.4 covers `p = n^(-1-η)` and
   Theorem 1.3 covers `p = n^(-1/2+η)` (artifact). Inside the range the groups are
   hyperbolic and the complexes are local spectral expanders
   (`random-complex-mid-range-pair-properties`). As recorded on
   `random-complex-missing-triangle-detected-by-quotient`, the groups have (T) and
   are not cubulated, so the Wise--Agol virtual specialness that makes low-density
   random groups residually finite is unavailable. No residual-finiteness or
   soficity theorem covering any mid-range exponent was found in the sources on
   main. The route is not killed by a known sofic regime; that is not evidence
   for (CPT).
2. **Small-n computation (2026-09-13): screened out, not run.** Every recorded
   way to decide (CPT) goes through finite quotients of `π_1(Y)`, whose
   asymptotic constraint is Meshulam's theorem. With natural logarithms, excluding
   quotients of order at most `n` needs `p >= 13 ln n / n`. That is compatible with
   the mid-range bound `p <= n^(-1/2)` only for `n >= 15795`, where
   `p ≈ 0.0080`, the complex has about `5.2·10^9` triangles and `1.2·10^8` edges.
   Order at most `n^2` needs `n >= 46133` and about `7.6·10^10` triangles. At
   `n = 40`, `η = 0.3`, `p ≈ 0.076` and there are about 750 triangles, while
   `6 ln n / n ≈ 0.55`. So quotient searches or cochain optimizations at feasible
   sizes probe no regime the theorem sees, and their output would say nothing
   about (CPT).
3. **Bounded removal (2026-09-13): the refutation side needs less than
   random-triangle detection.** `bounded-removal-finite-quotient-caps-cocycle-cheeger`
   (ESTABLISHED) caps `h_1(Z,Sym)` by `(2-2λ)t/((1-2λ)|(Z \ T)(2)|)` whenever a
   finite quotient of `π_1(Z \ T)` detects one removed perimeter. So (CPT) implies
   that for every fixed `t`, a.a.s. no bounded removal from `Y` leaves an expander
   with a detected removed perimeter. The matching open refutation premise is
   `random-complex-bounded-removal-detected-by-quotient`, wired in by
   `random-complex-cheeger-capped-via-bounded-removal`. Its quotients need not
   factor through `π_1(Y)`, so Meshulam's exclusion does not apply to them as
   stated.
