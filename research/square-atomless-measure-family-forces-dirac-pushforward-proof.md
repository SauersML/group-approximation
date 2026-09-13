---
rg: 2
id: square-atomless-measure-family-forces-dirac-pushforward-proof
kind: route
title: Lebesgue's covering theorem gives a level-set component of full diameter, and a Borel selection over its projection gives a Lebesgue-marginal measure on it
target: square-atomless-measure-family-forces-dirac-pushforward
requires: []
artifacts:
  - research/artifacts/ex2-tw-square-dirac-pushforward-2026-09-13.md
---

Proposition U of `research/artifacts/ex2-tw-square-dirac-pushforward-2026-09-13.md`.

1. **Factorization.** The components of the fibres of `f` form an upper semicontinuous
   decomposition. Its quotient `q: S → Γ` is monotone, and `f = g ∘ q` with `g` light. By Hurewicz's
   formula for closed maps, `dim Γ ≤ 1`.
2. **Cover.** If every component had diameter `< 1`, the maximum `d_0 < 1` would be attained.
   Pulling back a fine cover of `Γ` of order `≤ 2` gives an open cover of `S` of order `≤ 2` whose
   members have diameter `< 1`. None of them meets two opposite sides, contradicting Lebesgue's
   covering theorem for `[0,1]²`.
3. **Measure.** A component `C ⊆ f^{−1}(c)` with `diam C ≥ 1` projects onto an interval `J` of length
   `≥ 1/√2` in some coordinate `i`. By Kuratowski–Ryll-Nardzewski there is a Borel selection
   `s: J → C` with `p_i ∘ s = id`. Then `μ = s_*(Leb_J)` has `f_*μ = δ_c`.
4. **Family.** The measures with some coordinate marginal equal to `Leb_J`, `|J| ≥ 1/√2`, form a
   closed subset of `Prob(S)`: pass to convergent witnesses `(i, J)`. It is therefore compact. Its
   members are atomless because their marginals are.
