---
rg: 2
id: burau-kernel-restricts-along-strand-inclusion-proof
kind: route
title: "Burau kernels along strand inclusions: the unreduced Burau of B_{n+1} restricts to Burau of B_n plus a trivial line, and unreduced and reduced kernels agree"
target: burau-kernel-restricts-along-strand-inclusion
requires: []
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Full write-up: artifact §2.5.

- The unreduced Burau representation sends `σ_i` to `I_{i-1} ⊕ [[1-t, t],[1,0]] ⊕ I_{n-i-1}`. So
  for `i < n`, `ρ̃_{n+1}(σ_i) = ρ̃_n(σ_i) ⊕ 1`, hence `ρ̃_{n+1} ∘ f = ρ̃_n ⊕ 1` and
  `f(x) ∈ ker ρ̃_{n+1}` iff `x ∈ ker ρ̃_n`.
- Kernel membership is invariant under conjugation, so every inclusion from a subdisk missing
  the extra puncture behaves the same way.
- Reduced and unreduced kernels agree:
  - `v = (1,...,1)^T` is fixed, since each row of `[[1-t,t],[1,0]]` sums to 1;
  - `w = (1, t, ..., t^{n-1})` is a fixed covector, since `(t^{i-1}, t^i)[[1-t,t],[1,0]] = (t^{i-1}, t^i)`;
  - `w v = 1 + t + ... + t^{n-1} ≠ 0` in `Q(t)`.

  So `Q(t)^n = Q(t)v ⊕ ker w` as representations, `ρ̃_n ≅ 1 ⊕ ρ_n` over `Q(t)`, and the kernels
  over `Z[t^{±1}] ⊂ Q(t)` coincide. ∎
