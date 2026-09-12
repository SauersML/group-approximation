---
rg: 2
id: sl3z-ozawa-block-corona-has-unique-trace
kind: claim
title: The corona of Ozawa's SL(3,Z) block algebra has a unique trace, whose kernel is a nonzero traceless ideal
distinct_from:
  kazhdan-block-algebras-contain-their-block-ideal: that places the block ideal inside any Kazhdan block algebra; this computes the traces of the corona for Ozawa's SL(3,Z) blocks, using Bekka's character rigidity and the non-amenable point stabilizer of P²(Q).
  stw99-quasitrace-problem-for-cstar-simple-groups: that asks whether the unique trace of a reduced C*-simple group algebra is its unique quasitrace; this is a unique-trace statement for a non-reduced block corona, whose trace kernel is nonzero.
artifacts:
  - research/artifacts/quasitrace-kazhdan-block-corona-2026-09-12.md
---

**ESTABLISHED (derivation `sl3z-ozawa-block-corona-unique-trace-proof`, conditional on the
imports named there).**

**Setting.**
- `Γ = SL(3,Z)`, and `p_k → ∞` are distinct primes.
- `σ_k` is the permutation representation of `Γ` on `ℓ²(P²(F_{p_k})) ⊖ C1`.
- `B = C*(⊕_k σ_k(Γ))`, `I = ⊕_k M_{p_k² + p_k}` (inside `B` by
  `kazhdan-block-algebras-contain-their-block-ideal`), and `A = B/I`, with
  `ρ_∞ : Γ → A`.

**Then:**
1. `τ_0(x + I) = lim_k tr(x_k)` is a tracial state of `A` with
   `τ_0 ∘ ρ_∞ = δ_e`. Its GNS image is `C*_r(Γ)`, so `λ_Γ ≺ ρ_∞`.
2. `τ_0` is the only tracial state of `A`.
3. `λ_{Γ/P} ≺ ρ_∞`, where `P = Stab_Γ([1:0:0])` is not amenable. So the trace
   kernel `K = N_{τ_0} = ker(A → C*_r(Γ))` is nonzero.
4. `K` carries no nonzero bounded trace.

**Why it matters.** Quasitrace linearity of `B` is now decided by `K` alone
(`sl3z-ozawa-block-qt-linearity-iff-corona-kernel-invisible`). A bounded
2-quasitrace on `A` that charges `K` cannot be a trace.

**Imports, not re-derived:**
- Bekka, *Operator-algebraic superrigidity for SL_n(Z), n ≥ 3*, Invent. Math. 169
  (2007): every finite factor representation of `SL(n,Z)`, `n ≥ 3`, is
  finite-dimensional or extends to `L(Γ)`;
- Hulanicki–Reiter amenability criterion;
- irreducibility and pairwise inequivalence of the `σ_k`, from main.

Proofs are in §2 of the artifact.
