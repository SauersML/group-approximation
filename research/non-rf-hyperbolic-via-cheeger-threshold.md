---
rg: 2
id: non-rf-hyperbolic-via-cheeger-threshold
kind: route
title: The Chapman--Peled threshold puts a random triangle in the finite residual of a random hyperbolic group
target: non-residually-finite-hyperbolic-group
requires: [random-complex-cocycle-cheeger-beats-triangle-count, random-complex-mid-range-pair-properties, finite-quotient-caps-cocycle-cheeger-constant]
artifacts:
  - research/artifacts/chapman-peled-2509-21566-verified-2026-09-11.md
---

## Why sufficient

Fix `η` from the premise, `p = n^(-1+η)`, and `λ = 1/4`. Sample `(Y, Z, Δ)` by
adding a uniformly random missing triangle `Δ` to `Y ~ Y(n,p)`.

1. The a.a.s. lower bound `h_1 = ω(n^(-3)p^(-1))` transfers from `Y(n,p)` to
   `Z` (total-variation transfer in `random-complex-mid-range-pair-properties`).
2. A.a.s. `Y` is a `1/4`-local spectral expander, `|Y(2)| = (1+o(1)) p C(n,3)`,
   `π_1(Y)` is hyperbolic, and the perimeter of `Δ` is nontrivial in `π_1(Y)`.
3. The cap (FQC) is `(2-2λ)/((1-2λ)|Y(2)|) = 3/|Y(2)| = O(n^(-3)p^(-1))`. So a.a.s.
   `h_1(Z,Sym)` exceeds it. By the contrapositive of
   `finite-quotient-caps-cocycle-cheeger-constant`, the perimeter of `Δ` dies in
   every finite quotient of `π_1(Y)`.
4. For `n` large, some sample satisfies all of these. Its `π_1(Y)` is hyperbolic
   and has a nontrivial element in its finite residual, so it is not residually
   finite.

Neither soficity nor the Glebsky--Rivera step appears. The estimate reaches this
root directly, not only through `non-rf-hyperbolic-from-nonsofic-hyperbolic`.

## What the route teaches

The premise is at least as strong as the conclusion *for these specific random
groups*. The route is a genuine reduction, since the premise is a Cheeger bound
and can fail, but it is not a way around the finite-quotient problem. It is a
reformulation of that problem in expansion language.
