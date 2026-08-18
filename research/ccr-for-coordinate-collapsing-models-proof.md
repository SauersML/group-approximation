---
rg: 2
id: ccr-for-coordinate-collapsing-models-proof
kind: route
title: Per-coordinate Kazhdan uniformity plus image collapse
target: ccr-for-coordinate-collapsing-models
requires: [compressor-coset-two-point-exact]
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

# Per-coordinate Kazhdan uniformity plus image collapse

Fix a finite generating set `S` of `Λ` with Kazhdan constant `κ > 0`:
for EVERY unitary representation `ρ` of `Λ` on a Hilbert space `V` and
every `v ∈ V`,

```text
max_{s∈S} ‖ρ(s)v − v‖  ≥  κ · dist(v, V^{ρ(Λ)}) .            (K)
```

Let `x = (x_n) ∈ σ(Λ)' ∩ M`, `‖x‖ ≤ 1`.

**1. Exact commutation gives vanishing generator defects.**  For each
`s ∈ S`, `[x, σ(s)] = 0` in `M` means
`ε_n := max_{s∈S} ‖x_n − π_n(s) x_n π_n(s)^*‖₂ → 0` along `𝒰`
(finitely many generators, so the max also vanishes).

**2. Kazhdan uniformity per coordinate.**  Apply (K) to the
conjugation representation `ρ_n = Ad(π_n|_Λ)` of `Λ` on the Hilbert
space `(M_{d_n}, ‖·‖₂)` and the vector `x_n`:
`dist₂(x_n, Fix_n) ≤ ε_n / κ`, where `Fix_n` is the commutant of
`π_n(Λ)` in `M_{d_n}`.  Hence for EVERY `λ ∈ Λ`, not just generators,

```text
‖x_n − π_n(λ) x_n π_n(λ)^*‖₂  ≤  2 ε_n / κ ,                 (U)
```

uniformly in `λ` — the constant depends only on `(S, κ)`.

**3. Image collapse converts Γ-conjugation into Λ-conjugation.**  Let
`γ ∈ Γ`.  By hypothesis `π_n(γ) ∈ π_n(Γ) ⊆ π_n(Λ)` for 𝒰-most `n`, so
`π_n(γ) = π_n(λ_n)` for some `λ_n ∈ Λ` (depending on `n` — this is
where a fixed-`λ` argument would fail and (U)'s uniformity is
consumed).  Then by (U),

```text
‖x_n − π_n(γ) x_n π_n(γ)^*‖₂ = ‖x_n − π_n(λ_n) x_n π_n(λ_n)^*‖₂ ≤ 2ε_n/κ .
```

**4. Ultralimit.**  `‖[x, σ(γ)]‖₂ = lim_𝒰 ‖x_n π_n(γ) − π_n(γ) x_n‖₂
= lim_𝒰 ‖x_n − π_n(γ)x_nπ_n(γ)^*‖₂ ≤ lim_𝒰 2ε_n/κ = 0`, so
`x ∈ σ(Γ)' ∩ M`.  The reverse containment is `Λ ≤ Γ`.  ∎

**The congruence instance.**  For the Kun–Thom pair take the chain of
congruence quotients `Q_M = EL_r(𝔽_q[(ℤ/M)^d]) ⋊ SL_d(ℤ/M)` with their
regular representations: `σ` is trace-faithful (`tr σ(g) → 0`,
`g ≠ e`), `Λ = tΓt⁻¹` is finitely generated with property (T)
(`Λ ≅ Γ = EL_r(𝔽_q[x₁…x_d])`, `r ≥ 3`), and the image collapse
`π_M(Λ) = π_M(Γ) = E` holds because the elementary part is normal in
`Q_M` and `π_M(Γ)` is all of it (the computation recorded in
`compressor-coset-two-point-exact`).  All hypotheses check; (CCR)
holds for this `σ`.

**Why this does not close `kt-centralizer-normalization-hs`.**  Steps
1–2 survive for arbitrary `σ` (indeed `x ∈ σ(Λ)'` is exactly
`Λ`-invariant, no Kazhdan needed at the ultraproduct level).  Step 3
is the wall: for a representation with only APPROXIMATE coordinate
homomorphisms there are no `π_n(γ)`, `π_n(λ_n)` to compare, and no
congruence topology to collapse the compression.  The open remainder
is precisely: transport (U) across the approximate-vs-genuine
homomorphism gap — the same locus as Alekseev–Thom OP 6.2, as
recorded in the parent node's excess-commutant analysis.
