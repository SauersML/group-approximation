---
rg: 2
id: random-complex-bounded-removals-stay-expanders-proof
kind: route
title: Expansion of the sampled complex, a Chernoff bound on edge degrees, then the link perturbation bound for every bounded removal
target: random-complex-bounded-removals-stay-local-expanders
requires: [local-spectral-expansion-survives-bounded-triangle-removal, random-complex-mid-range-pair-properties]
---

## Why sufficient

Fix `t`, `η` and `p = n^(-1+η)`, and sample `Y ~ Y(n,p)`.

1. **Expansion of `Y`.** Item 3 of `random-complex-mid-range-pair-properties`,
   with `λ = 1/8`, says the sampled complex is a `1/8`-local spectral expander
   a.a.s. That complex is `Y ~ Y(n,p)`: Algorithm 1 samples `Y` first. Its
   underlying fact is Chapman--Peled's import of
   Hoffman--Kahle--Paquette Theorem 1.1, valid for `p = ω(log n / n)`.
2. **Edge degrees.** The number of triangles of `Y` containing a fixed edge is
   `X ~ Bin(m, p)` with `m = n - 2`. For `s > 0`,
   `E[e^(-sX)] = (1 - p + p e^(-s))^m <= exp(mp(e^(-s) - 1))`.
   - **Tail.** Markov's inequality with `s = ln 2` gives
     `Pr[X <= mp/2] <= exp(s mp/2 + mp(e^(-s) - 1)) = exp(-mp(1 - ln 2)/2) <= exp(-0.15 mp)`.
   - **Union.** Over the `C(n,2)` edges this is at most
     `n^2 exp(-0.15 (n-2) p) -> 0`, because `(n-2)p = (1+o(1)) n^η`.
   - So a.a.s. every edge lies in at least `d = (n-2)p/2` triangles. In
     particular `Y` is pure.
3. **Every bounded removal.** On the intersection of 1 and 2, take any `T ⊂ Y(2)`
   with `|T| <= t`.
   - **Perturbation.** `local-spectral-expansion-survives-bounded-triangle-removal`
     applies with `λ = 1/8`, since `t < d` for large `n`. `Y \ T` is pure, and
     it is a `λ'`-local spectral expander with
     `λ' = 1/8 + (t + sqrt(2t))/((n-2)p/2 - t) = 1/8 + O(t n^(-η))`.
     That is at most `1/4` for all large `n`.
   - **Connectivity.** The 1-skeleton of `Y \ T` is `K_n`, so it is connected.

Steps 1 and 2 do not depend on `T`, so the conclusion holds for all `T` at once.
