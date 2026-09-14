---
rg: 2
id: turing-degrees-contain-continuum-antichains-proof
kind: route
title: A finite-extension perfect tree defeats every Turing functional on every ordered pair of distinct branches
target: turing-degrees-contain-continuum-antichains
requires: []
artifacts:
  - research/artifacts/sk-free-7-non-embeddability-2026-09-13.md
---

Complete direct proof. Φ_0, Φ_1, … is an enumeration of Turing functionals, and Φ_e^τ(n)↓ means convergence within |τ| steps using only the oracle string τ.

**Construction.** Define binary strings σ_s for s ∈ 2^{<ω} by stages, keeping the strings σ_s (s ∈ 2^n) pairwise incomparable at stage n.
- **Stage 0.** σ_∅ = ∅.
- **Stage n.** Handle the requirements R(e,s,t), for e < n and ordered pairs s ≠ t in 2^n, one after another. Each step replaces some current strings by extensions; extending preserves incomparability.
- **Handling R(e,s,t).** Let m = |σ_t|.
  - **Case 1.** Some τ ⊇ σ_s and some n′ ≥ m have Φ_e^τ(n′)↓. Replace σ_s by τ, and σ_t by an extension ρ with |ρ| > n′ and ρ(n′) ≠ Φ_e^τ(n′).
  - **Case 2.** Otherwise do nothing.
- **Splitting.** After all requirements of stage n, put σ_{s⌢i} = σ_s⌢i for i ∈ {0,1}.

**Verification.**
- **A perfect set.** For f ∈ 2^ω let x_f = ⋃_n σ_{f|n}. Distinct f, g split at some level, so x_f ≠ x_g. So P = {x_f} is perfect, of cardinality 2^{ℵ_0}.
- **Incomparability.** Let f ≠ g and fix e. Choose n > e with s = f|n ≠ t = g|n. At stage n, R(e,s,t) was handled, and x_f, x_g extend the strings current after that step.
  - In Case 1, x_f ⊇ τ gives Φ_e^{x_f}(n′) = Φ_e^τ(n′) ≠ ρ(n′) = x_g(n′).
  - In Case 2, no extension of σ_s makes Φ_e(n′) converge for any n′ ≥ m, so Φ_e^{x_f} is not total and Φ_e^{x_f} ≠ x_g.
  - As e is arbitrary, x_g ≰_T x_f. By symmetry, using R(e,t,s), x_f ≰_T x_g.
- **Degrees.** Pairwise incomparable reals have pairwise distinct degrees, and these degrees form an antichain.

**Model test.** Dropping Case 2 would demand convergence that may never happen; the case split is what makes the construction non-effective and total.
