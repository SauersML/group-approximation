---
rg: 2
id: amenable-full-group-forces-invariant-measure-proof
kind: route
title: Markov-Kakutani measure made groupoid-invariant by 3-cycle realization
target: amenable-full-group-forces-invariant-measure
requires: []
artifacts:
  - research/artifacts/fp-simple-amenable-full-groups-2026-09-12.md
---

## Why sufficient

1. **3-cycles.** Suppose `U(x) = y != x`. Pick `z` in the orbit, different from
   `x` and `y`, and a bisection `V` with `V(y) = z`. On a clopen `E` containing
   `x`, small enough that `E`, `U(E)` and `VU(E)` are disjoint, let `a` swap `E`
   and `U(E)` through `U`, and `b` swap `E` and `VU(E)` through `VU`. Then
   `[a,b] = abab` restricts to `U` on `E`, and lies in `D([[G]])`.
2. **Invariant measure.** An amenable `Gamma` acting on compact `X` has an
   invariant probability measure `mu`, by the fixed point property on the
   compact convex set of measures.
3. **Moving germs.** Where `U` moves `x`, realization gives
   `mu(U(E)) = mu(E)` near `x`.
4. **Fixed germs.** Where `U(x) = x`, choose a bisection `W` moving `x` to some
   `z != x`, and write `U = (U W^{-1}) W`. Both factors move the relevant point.
5. **Globalize.** A finite clopen partition of `s(U)` subordinate to these
   neighbourhoods, together with injectivity of `U`, gives `mu(U(E)) = mu(E)`
   for all Borel `E`.
6. **Corollary.** The largest open null set is invariant, so under minimality
   `mu` has full support. Then `mu(A) >= mu(B) + mu(C) = 2 mu(A) > mu(A)`.
7. **SFT example.** `[a] = ⊔_b [ab]` with `[ab] ~ [b]` turns an invariant
   measure into a positive vector `v = Av`. So `rho(A) = 1`, and an irreducible
   0-1 matrix with `rho(A) = 1` is a permutation matrix.
