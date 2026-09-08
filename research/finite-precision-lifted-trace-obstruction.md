---
rg: 2
id: finite-precision-lifted-trace-obstruction
kind: claim
title: Finite polynomial lifts give exact trace obstructions with a finite-subgroup precision bound
distinct_from:
  lifted-trace-detects-finite-subgroup-projectives: that constructs the p-adic invariant and proves nonvanishing; this gives an explicit terminating polynomial lift at each precision and a sufficient precision in terms of matrix size and subgroup order.
  leavitt-balanced-corners-separated-modulo-four: that treats one designated pair at precision two; this works for every prime, group, matrix size, and positive precision.
artifacts:
  - research/artifacts/kaplansky-finite-precision-trace-2026-09-07.md
  - experiments/kaplansky_trace_certificate.py
  - experiments/test_kaplansky_trace_certificate.py
  - research/artifacts/kaplansky-trace-certificates.json
---

For every prime p, group G, and k>=1 there is an additive invariant

    t_(p,k): K_0(F_p[G]) -> Z/p^k Z.

For an idempotent e it is the diagonal identity-coefficient trace of an
idempotent lift modulo p^k. Starting with any coefficient lift a, at most
ceil(log_2 k) iterations a <- 3a^2-2a^3 produce such a lift. This is a
finite polynomial construction; an executable calculation requires exact
group arithmetic, not merely an arbitrary presentation.

If AB=I, the idempotent d=I-BA has t_(p,k)([d])=0 for every k. Equivalent
projectives, including those isomorphic after a common stabilization, have
equal invariants. A nonzero difference is an obstruction; zero is inconclusive.

If 0!=e belongs to M_n(F_p[H]) for a finite subgroup H<=G, let
m'=|H|/p^(v_p(|H|)). Then t_(p,k)([e])!=0 whenever p^k>n m'. Hence
1+floor(log_p(n m')) is a sufficient detection precision for such an e,
and for a nonzero difference of nested idempotents supported in H.

This is a finite certificate form of the established lifted-trace method.
It does not assert faithfulness for arbitrary ambient projectives or solve
Kaplansky's conjecture.
