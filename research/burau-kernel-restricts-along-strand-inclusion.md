---
rg: 2
id: burau-kernel-restricts-along-strand-inclusion
kind: claim
title: "Adding a strand does not change Burau kernels: for the standard inclusion f of B_n in B_{n+1}, f(x) is in ker rho_{n+1} iff x is in ker rho_n"
artifacts:
  - research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md
---

Let `f : B_n → B_{n+1}` be the standard inclusion `σ_i ↦ σ_i` (`i < n`). Equivalently, `f` extends
mapping classes of a subdisk `D_n ⊂ D_{n+1}` that misses the extra puncture by the identity. Any
other such subdisk gives a conjugate inclusion.

Then for every `x ∈ B_n`, `f(x) ∈ ker ρ_{n+1}` iff `x ∈ ker ρ_n`, where `ρ` is the reduced Burau
representation. The same holds for the unreduced representation, whose kernel is the same.

This is the implication arXiv:2607.05283v1 needs when it proves `f(Φ) ∉ ker ρ_5` and concludes
`Φ ∉ ker ρ_4` (Theorem 6.6). Route: `burau-kernel-restricts-along-strand-inclusion-proof`.
