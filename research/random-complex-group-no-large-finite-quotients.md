---
rg: 2
id: random-complex-group-no-large-finite-quotients
kind: claim
title: Mid-range random complex groups have no nontrivial finite quotient of superpolynomial order
distinct_from:
  meshulam-random-complex-no-polynomial-quotients: that excludes quotients of order at most n^c by a counting argument; this excludes all larger ones, where first-moment counting over cochains fails because the entropy of Sym(N)-labels outgrows the n^η energy per edge
  random-complex-cocycle-cheeger-beats-triangle-count: that is a Cheeger bound implying only that random missing triangles die in finite quotients; this asks that there be no nontrivial finite quotients beyond polynomial order at all
---

**OPEN, conjectural.** For some `0 < η < 1/2` and some fixed `c > 0`, with
`p = n^(-1+η)`, a.a.s. `π_1(Y(n,p))` has no nontrivial finite quotient of order
greater than `n^c`.

Together with Meshulam's theorem this makes `π_1(Y)` a nontrivial hyperbolic
group with no nontrivial finite quotient
(`non-rf-hyperbolic-via-random-complex-no-finite-quotients`).

**Why counting stops at polynomial order.** Take a cochain `α` in star gauge
that differs from a coboundary on `k` edges. It violates at least about `n k/3`
triangles of the full simplex, and each must be absent from `Y`, costing a factor
`exp(-n^η/3)` per edge. The labels contribute entropy about `k(2 log n + log|G|)`.
First moment fails once `log|G| >~ n^η`, so the large-quotient regime needs a
structural argument: property (T) of every connected covering, or an expansion
statement about coverings.
