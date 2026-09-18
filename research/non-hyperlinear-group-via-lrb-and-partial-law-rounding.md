---
rg: 2
id: non-hyperlinear-group-via-lrb-and-partial-law-rounding
kind: route
title: A large odd exponent free Burnside group is non-hyperlinear if the local restricted Burnside principle holds and approximate exponent traces round to exact partial Burnside representations
target: non-hyperlinear-group
requires:
  - large-odd-exponent-local-restricted-burnside
  - approximate-exponent-traces-round-to-partial-burnside-reps
  - hs-burnside-iff-lrb-and-partial-law-trace-rounding
  - free-burnside-is-a-limit-of-hyperbolic-groups
---

Take `m >= 2` and odd `N >= n_1(F_m)` given by
`large-odd-exponent-local-restricted-burnside`, so `LRB(R_0, C)` holds for some
`R_0, C`. By `approximate-exponent-traces-round-to-partial-burnside-reps`,
`S(m,N,R_0)` holds. By clause (c) of
`hs-burnside-iff-lrb-and-partial-law-trace-rounding`, every `m`-generated
hyperlinear group of exponent dividing `N` is finite. `B(m,N)` is `m`-generated
of exponent dividing `N`, and it is infinite by item 4 of
`free-burnside-is-a-limit-of-hyperbolic-groups` (with `G = F_m`). So `B(m,N)`
is not hyperlinear. ∎

Both prerequisites are necessary for this exponent's finiteness input: clauses
(a) and (b) of the decomposition. The first also yields a non-residually-finite
hyperbolic group (`non-rf-hyperbolic-group-via-local-restricted-burnside`). The
second contains no finiteness statement. Operator-level proofs of it, through
stability of `Π_{R_0}(m,N)`, already produce a finitely presented
non-hyperlinear group (clause (d)).
