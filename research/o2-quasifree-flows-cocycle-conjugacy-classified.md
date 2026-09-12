---
rg: 2
id: o2-quasifree-flows-cocycle-conjugacy-classified
kind: claim
title: Distinct positive-parameter quasifree flows on the Cuntz algebra O2 are never cocycle conjugate
artifacts:
  - research/artifacts/stw99-lv-quasifree-flow-solution-2026-08-30.md
---

For irrational `λ, μ > 0`, the quasifree flows `α^{(λ)}, α^{(μ)}` on
`O_2` (`α^{(λ)}_t(s_1) = e^{it}s_1`, `α^{(λ)}_t(s_2) = e^{iλt}s_2`)
are cocycle conjugate if and only if `λ = μ`.  The separating
invariant is the unique KMS inverse temperature `β(λ)`, the root of

```text
e^{-β} + e^{-λβ} = 1,
```

which is strictly decreasing in `λ` and is recovered from the pair
(crossed product, dual flow) as the trace-scaling exponent of the dual
flow on the unique tracial ray.

This answers STW Problem LV
(`stw99-problem-lv-quasifree-flows-o2`) for plain cocycle conjugacy:
the classification is trivial — no two distinct parameters are
identified.  (If one instead allows cocycle conjugacy AFTER time
rescaling, the same invariant classifies up to the rescaling of `β`,
and the generator swap `s_1 ↔ s_2` realizes `λ ↔ 1/λ` after rescaling
time by `λ`; the plain question STW pose does not permit rescaling.)
