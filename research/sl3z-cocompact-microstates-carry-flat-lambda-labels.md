---
rg: 2
id: sl3z-cocompact-microstates-carry-flat-lambda-labels
kind: claim
title: Below a fixed scale, a microstate of SL3(Z) on SL3(R)/Λ is a Λ-labelled almost-action on V × Λ, flat on good relator cycles, whose finite orbits cost a fixed fraction of defects
artifacts:
  - research/artifacts/sl3z-cocompact-quotient-holonomy-drift-2026-09-13.md
distinct_from:
  uniquely-ergodic-action-sofic-iff-topological-microstates: that says microstates are the right models; this is the rigid normal form every microstate of this action has, forced by discreteness of Λ
---

**ESTABLISHED (unreviewed).** Let `Λ <= SL_3(R)` be cocompact, with `S = {e_ij^(±1)}`, finite
presentation `⟨S | R⟩` of `SL_3(Z)`, a right-invariant metric `d` and a compact `F` with `FΛ = SL_3(R)`.
There is `ε_0 > 0` with the following properties. Let `V` be finite, let `σ_s ∈ Sym(V)` be arbitrary,
let `y(v) = g_vΛ` with `g_v ∈ F`, and fix `ε < ε_0`. Call `(v,s)` good when
`d̄(y(σ_s v), s·y(v)) < ε`.

1. **Labels.** For each good pair there is exactly one `λ(v,s) ∈ Λ` with `d(g_(σ_s v), s g_v λ(v,s)) < ε`.
2. **Flatness.** Along any relator cycle whose pairs are all good, the product of the labels is `1`.
3. **Labelled system.** `σ̃_s(v,μ) = (σ_s v, λ(v,s)^(−1)μ)` on `Ω = V × Λ` commutes with right
   `Λ`-translation. `Φ(v,μ) = g_v μ` satisfies `d(Φ(σ̃_sω), sΦ(ω)) < ε` on good pairs and `<= diam(X)`
   on all pairs. On an honest finite action with every pair good, `SL_3(Z)` acts on `Ω`, and the
   stabilizers are the kernels of holonomy homomorphisms `ρ_v : Γ_v → Λ`.
4. **Finite labelled orbits cost defects.** There is `θ_* > 0` such that, once `ε` is small, every finite
   `σ̃`-invariant `O ⊆ Ω` has at least a proportion `θ_*` of bad pairs. This follows from
   `sl3-norm-drift-excludes-finite-almost-invariant-configs`.

So every microstate is a discretized measure-equivalence coupling. Any finite part of its holonomy
is paid for by defects. For `Λ = SL_3(Z)` (not cocompact) the Hecke models have all pairs good and
Hecke conjugations as holonomy, with infinite image.

Proof in `sl3z-cocompact-microstates-carry-flat-lambda-labels-proof`.
