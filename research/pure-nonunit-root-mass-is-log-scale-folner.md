---
rg: 2
id: pure-nonunit-root-mass-is-log-scale-folner
kind: claim
title: Under vertex rounding, pure non-unit root mass beyond depth one is at most the transport defect times the number of d-adic depth scales
distinct_from:
  compressor-transport-exactifies-under-vertex-rounding: that is the total-variation invariance of root spectra under the compressor; this applies it to the depth filtration by powers of x_1...x_d, where the compressor contracts depth by a factor d.
  nonunit-projection-bounded-by-root-spectral-mass: that bounds the non-unit projection by non-unit root mass; this bounds the pure non-unit part of that mass at depth above one.
  theorem-e-vertex-rounds-to-unit-type-representations: that is the open rounding statement; this is an established partial vanishing theorem, leaving shallow and mixed non-unit mass.
artifacts:
  - research/artifacts/nh-unit-type-rounding-2026-09-12.md
---

**ESTABLISHED.** Setting and hypotheses of `compressor-transport-exactifies-under-vertex-rounding`,
with `η_n = 4δ_n^2/κ^2` and `z = x_1 ⋯ x_d`. For a character `χ` of `(R_+, +)` put
`depth(χ) = min{k >= 0 : χ is trivial on z^k R_+}`, or `∞` if there is no such `k`.

1. **Depth versus type.** For `χ` killing `I_n`, `depth(χ) < ∞` iff `χ` is trivial on the unit factor `A_u`, so the
   character is purely non-unit. Mixed and unit-type characters have depth `∞`.
2. **Contraction.** `depth(χ ∘ φ_A) <= ⌈depth(χ)/d⌉`.
3. **Per-scale bound.** Every d-adic block carries little mass: `μ_n(d^j < depth <= d^(j+1)) <= η_n` for all `j >= 0`.
4. **Total bound.** `μ_n(1 < depth < ∞) <= η_n · (1 + log_d(r(r-1)n'))`.

**Reading.**
- **Where pure non-unit mass above depth one can live.** It must spread over at least `1/η_n` d-adic
  depth scales. This is the Følner escape along the amenable cyclic compressor direction. The mass
  vanishes whenever `δ_n^2 log n -> 0` along `U`.
- **What stays open** in `theorem-e-vertex-rounds-to-unit-type-representations`:
  - that slow-rate spread;
  - shallow pure non-unit mass, i.e. characters of `R_+/(z)`, where `D_A` does not contract;
  - mixed constituents, which are nontrivial on both factors.

Derivation: `pure-nonunit-root-mass-folner-proof`.
