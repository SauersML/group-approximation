---
rg: 2
id: trace-problem-convergent-sequence-boundaries-proof
kind: route
title: Atomic disintegration, spectral cut, and m orthogonal copies that are sections because their 2-norms vanish at the limit
target: trace-problem-holds-over-convergent-sequence-boundaries
requires: []
artifacts:
  - research/artifacts/stw99-xxii-trace-problem-2026-08-30.md
---

Separate the finitely many limit points by clopen sets; it suffices to
treat `K = {z_1, z_2, …} ∪ {∞}` with `z_n → ∞` and every `z_n` isolated.
Let `φ` be a tracial state on `M`.

**Atomic disintegration.**  `φ|_{C(K)} = Σ_n μ_n δ_{z_n} + μ_∞ δ_∞`.  For
each `n`, `a ↦ φ(χ_{z_n} a)/μ_n` (when `μ_n > 0`) is a trace killing the
complementary clopen set, hence factoring through the fibre factor `R_{z_n}`,
hence equal to `τ_{z_n}` (finite factors have a unique tracial state, by the
Dixmier property).  The residual functional `ν(a) = lim_N φ(χ_{tail_N} a)`
is a positive tracial functional of mass `μ_∞` killing every `χ_{z_n}`; if
`μ_∞ = 0` then `φ = Σ μ_n τ_{z_n}` σ-additively and we are done.  Otherwise
`ψ := ν/μ_∞` is a trace with central measure `δ_∞`, and it remains to show
`ψ` kills `I_∞ = {b : b(∞) = 0}`; then `ψ` factors through the fibre at `∞`
and equals `τ_∞`, so `φ = Σ μ_n τ_{z_n} + μ_∞ τ_∞`, which is
`‖·‖_{2,X}`-continuous.

**Killing `I_∞`.**  Let `0 ≤ b ≤ 1` with `b(∞) = 0`, so
`ε_n := ‖b(z_n)‖_{2}^2 → 0`.  Fix `η > 0` and set
`e_n := 1_{[η,1]}(b(z_n))`, a projection in the fibre with
`τ_{z_n}(e_n) ≤ ε_n/η^2 → 0`, and `b(z_n) ≤ η + e_n`.  The assignment
`e = (e_n)_n`, `e(∞) = 0`, is a *section*: each coordinate is free (`z_n`
isolated) and `‖e_n‖_2 → 0` gives 2-continuity at `∞`.  So
`ψ(b) ≤ η + ψ(e)`.

Fix `m ∈ N`.  For every `n` with `m τ_{z_n}(e_n) ≤ 1` choose in the finite
factor `R_{z_n}` partial isometries `v_{1,n}, …, v_{m,n}` with
`v_{i,n}^* v_{i,n} = e_n` and mutually orthogonal ranges (possible since
`m τ(e_n) ≤ 1`); for the finitely many other `n` set `v_{i,n} = 0`.  Each
`v_i = (v_{i,n})_n`, `v_i(∞) = 0`, is a section (`‖v_{i,n}‖_2^2 = τ(e_n) → 0`).
Then `Σ_i v_i v_i^* ≤ 1` fibrewise, and by traciality
`ψ(v_i e v_i^*) = ψ(e^{1/2} v_i^* v_i e^{1/2}) = ψ(e)` up to a finitely
supported (hence `ψ`-null) correction.  Summing,
`m ψ(e) ≤ ψ(Σ_i v_i v_i^*) ≤ 1`.  As `m` was arbitrary, `ψ(e) = 0`, so
`ψ(b) ≤ η` for all `η`, so `ψ(b) = 0`.
