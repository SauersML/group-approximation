---
rg: 2
id: atlas-stabilizer-commutant-no-go-proof
kind: route
title: An exactly forced cross-commutation, killed by quasisimplicity in the ultraproduct
target: atlas-stabilizer-commutant-no-go
requires: [atlas-steinberg-rank-five-translation, atlas-relator-central-sufficiency]
artifacts:
  - research/artifacts/hyperlinear-q34-audit-2026-08-16.md
---

# An exactly forced cross-commutation, killed by quasisimplicity

**1. The forced relation.**  Decompose `A₈` into the 15 right cosets `M g_i`,
so `ℓ²(A₈) ≅ ℓ²(M) ⊗ ℂ¹⁵` and `λ|_M ≅ λ_M ⊗ I₁₅`; at multiplicity `k` the
first chart restricted to `M` is `λ_M(m) ⊗ I_{15k}`.  For `D ∈ π₁(M)′` we have
`[D, π₁(m)] = 1`, hence also `[D*, π₁(m)] = 1` (take adjoints and let `m` run
over `M`).  Since `J L_b J* = R_b` and left and right regular translations
commute, `π₂(b) = D R_b D*` commutes with `π₁(m)`:

```text
[π₁(m), π₂(b)] = 1        exactly,  for all m ∈ M, b ∈ A₈.
```

`I_{ℓ²(M)} ⊗ U(15k) ⊆ π₁(M)′`, so this covers the Stage-1 family.

**2. The witness word.**  `p₀₁ = I + E₀₁` fixes `e₀` under `A₈ ≅ GL₄(𝔽₂)`,
hence lies in the stabilizer `M`, so step 1 applies to it.  Put
`c = [p¹₀₁, p²₁₀]`, of free-product length four.  The exact binary-Leavitt
normal-form evaluator gives `leavitt_is_one = False` (12 surviving monomials),
so `c ∉ ker(P̄ ↠ Q)`.  Consistency: `c` does lie in `ker(P̄ ↠ A₈ × A₈)`, being
a cross-chart commutator — it is a cartesian escapee, not a relator, exactly
as `atlas-true-criterion-baseline` predicts of this kernel.

**3. Ultraproduct.**  Suppose `k_n` and `D_n ∈ π₁(M)′` gave
`max_{s ∈ T_St} ‖π_{D_n J}(s) − I‖₂ → 0`.  Each chart is an exact
representation of `A₈`, so each `n` gives a genuine homomorphism
`P̄ → U(20160k_n)`; in the tracial matrix ultraproduct every `s ∈ T_St` maps to
`1`, so the map factors through `E = P̄/⟨⟨T_St⟩⟩`, giving

```text
Ψ : E ⟶ U(∏_ω M_{20160 k_n}) .
```

**4. Nontriviality.**  Chart 1 is untouched by `U`, so for `x, y ∈ A₈` with
`[x, y] ≠ 1` the normalized-HS commutator defect is `√2` at every `n`
(`λ(g) ⊗ I_k` is at distance `√2` from `I` for `g ≠ 1`).  Hence `Ψ ≠ 1`.

**5. Contradiction.**  By `atlas-relator-central-sufficiency`, `E` is a perfect
central extension of the nonabelian simple `Q`, hence quasisimple: every proper
normal subgroup is central.  `ker Ψ` is proper by step 4, so `ker Ψ ≤ Z(E)`.
Step 1 gives `π_{D_n J}(c) = I` exactly at every `n`, so `c ∈ ker Ψ ≤ Z(E)`.
But `Z(E)` maps into `Z(Q) = 1` (the map `E ↠ Q` is onto, so the image of a
central element is central), so `c` would die in `Q`, contradicting step 2. ∎

The bound is uniform because the contradiction is derived from an arbitrary
defect-vanishing *sequence*, with `k_n` unconstrained — nothing in the argument
sees the multiplicity.
