---
rg: 2
id: sl3z-ozawa-corona-trace-kernel-has-property-s
kind: claim
title: The trace kernel of Ozawa's SL(3,Z) block corona has Ortega–Perera–Rørdam property (S), equivalently no bounded 2-quasitrace
distinct_from:
  sl3z-ozawa-corona-trace-kernel-is-stable: that asks for stability of K; this asks for the weaker comparison property (S) (a ⊥ b with a stably dominated by b, instead of a ≾ b), which stability implies and which is equivalent to K carrying no nonzero bounded 2-quasitrace.
  sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible: that is the dichotomy on whether quasitraces of the corona vanish on K; this is an intrinsic property of K alone, sufficient for that vanishing.
  sl3z-ozawa-corona-trace-kernel-is-unique-maximal-ideal: that proves K has no unital quotient, which is what makes (S) equivalent to having no bounded quasitraces here; this is the remaining open quasitrace half.
artifacts:
  - research/artifacts/quasitrace-kernel-maximal-ideal-property-s-2026-09-12.md
---

**Statement (OPEN).** Notation as in `sl3z-ozawa-block-corona-has-unique-trace`:
`A = B/I`, and `K = ker(A → C*_r(SL(3,Z)))` is the trace kernel. The claim is that `K`
has property (S):
- for every `a ∈ F(K)` there is `b ∈ K_+` with `a ⊥ b` and `(k+1)⟨a⟩ ≤ k⟨b⟩` in `W(K)`
  for some `k`;
- here `F(K)` is the set of `a ∈ K_+` with `ae = a` for some `e ∈ K_+`.

**Equivalent form (proved, artifact Prop 2.1).**
`sl3z-ozawa-corona-trace-kernel-is-unique-maximal-ideal` shows that `K` has no nonzero
unital quotient. So Ortega–Perera–Rørdam (arXiv:0903.2917v4) Prop 4.5 makes the claim
equivalent to: **`K` admits no nonzero bounded 2-quasitrace**.

**Why it matters.**
- The claim implies that every bounded 2-quasitrace on `A` vanishes on `K`. So
  `sl3z-ozawa-block-algebra-quasitraces-are-traces` follows, through
  `sl3z-ozawa-block-qt-via-kernel-property-s`.
- It is weaker than `sl3z-ozawa-corona-trace-kernel-is-stable`: OPR §4 says stable
  algebras have (S).
- By OPR Prop 4.7, it is equivalent to stability when `Cu(K)` has ω-comparison.
- The converse would take "every quasitrace of `A` vanishes on `K`" back to (S). That
  needs bounded 2-quasitraces on `K` to extend to `A`, and it is not settled.

## Attempts

- **Through stability.** This reduces to `sl3z-ozawa-corona-trace-kernel-is-stable`,
  which is open.
  - The ideal-theoretic obstruction there is ruled out.
  - The one-translate criterion (artifact Prop 2.3) is sufficient: `‖a · uau*‖` small
    for a unitary `u ∈ A`.
  - It holds with `u = ρ_∞(g)`, `g ∉ P`, for the rank-one parabolic block projections,
    but only if those lie in `B`, which is not decided. For general `a ∈ K_+` it is
    unknown.
- **Direct witnesses from group translates.** For `u = ρ_∞(g)`, the orthogonality is
  controlled by matrix coefficients of `σ_k(g)` on the range of `a_k`.
  - Consider the spectral elements `f(h) ∈ K`, where `h = Σ_s Re ρ_∞(s)` and `f`
    vanishes on `sp λ_Γ(h)`. Their ranges are Schreier-graph eigenspaces with no
    localization information.
  - This dies without strong-convergence information on `σ_k`.
- **Ghost part.** `K ⊃ B ∩ Ghost(C*_u(⊔ X_k))`. No stability statement and no
  quasitrace statement for the ghost part was obtained. The Willett–Yu and HLS sources
  were not read in this lane.
