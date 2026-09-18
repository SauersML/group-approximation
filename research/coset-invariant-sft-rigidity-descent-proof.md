---
rg: 2
id: coset-invariant-sft-rigidity-descent-proof
kind: route
title: Pull the quantum family back to Λ/Δ with the local Δ-invariance rule, then induct on the complexity of pair types through operator determinism identities
target: coset-invariant-sft-rigidity-descends-along-double-cosets
requires: [fp-v-times-subshift-full-groups-force-quantum-rigidity]
---

The notation is that of the target. Fix a `D`-quantum family `E` with `D ≥ D_0`. All products below
are of operators indexed by points of one ball `B_D(p)`, which pairwise commute by (Q2) because such
points are at distance `≤ 2D`.

**Local expansion lemma.** Let `p ∈ Λ`, let `P` be a set of patterns on a subset `Y ⊆ B_D(p)`, and
suppose no pattern in `P` occurs in `X`. Then `∏_(y ∈ Y) E_(σ(y))(y) = 0` for every `σ ∈ P`.
- Multiply by `∏_(y ∈ B_D(p) \ Y) (Σ_b E_b(y)) = 1`, which is (Q1).
- Expand and reorder, which is allowed since everything in `B_D(p)` commutes.
- Each term is the product over a full `B_D(p)`-pattern extending `σ`. That pattern does not occur in
  `X`, so the term vanishes by (Q3).

**1. Δ-invariance.** Take `δ ∈ Σ_Δ` and `λ`. Both `λ` and `λδ` lie in `B_D(λ)`. The pattern
`(a at λ, b at λδ)` with `a ≠ b` does not occur in `X`, so the lemma gives `E_a(λ) E_b(λδ) = 0`. Then
- `E_a(λ) = E_a(λ) Σ_b E_b(λδ) = E_a(λ) E_a(λδ)`,
- `E_a(λδ) = Σ_b E_b(λ) E_a(λδ) = E_a(λ) E_a(λδ)`,

so `E_a(λ) = E_a(λδ)`. Chaining over words in `Σ_Δ` gives invariance under all of `Δ`.

**2. Short types.** If the type of `(ω, ω')` has span `≤ 2D`, pick lifts at distance `s(θ) ≤ 2D`
(possible by right-translating lifts inside their cosets). Then (Q2) applies to them, and by 1 these
operators are `F(ω)` and `F(ω')`.

**3. Determinism identity.** In the step, let `φ : A^T -> A` be the function with `x(λ') = φ(x|_(λ'T))`
on `X`. Since `T ⊆ B_D`, the set `{λ'} ∪ λ'T` lies in `B_D(λ')`, and the lemma applies.
- For `σ ∈ A^T`, the pattern `(a at λ', σ on λ'T)` does not occur when `φ(σ) ≠ a`.
- Hence `E_a(λ') = Σ_σ E_a(λ') ∏_t E_(σ(t))(λ't) = Σ_(φ(σ) = a) E_a(λ') ∏_t E_(σ(t))(λ't)`.
- For `φ(σ) = a`, every other letter `a' ≠ a` kills `∏_t E_(σ(t))(λ't)`. So
  `E_a(λ') ∏_t E_(σ(t))(λ't) = ∏_t E_(σ(t))(λ't)`.

Therefore `F_a(ω') = E_a(λ') = Σ_(φ(σ) = a) ∏_(t ∈ T) F_(σ(t))(π(λ't))`, a polynomial in the
`F(π(λ't))`.

**4. Induction on `c`.** Claim: `[F_a(ω), F_b(ω')] = 0` for all pairs of type `θ`, all letters.
- If `c(θ) ≤ c_0`, this is 2, by (base).
- If `c(θ) > c_0`, by (descent) and induction `F(ω)` commutes with every `F(π(λ't))`, hence with the
  polynomial of 3, which is `F(ω')`.

`c` takes values in `N`, so the induction is well founded. Every pair of points of `Ω` has some type,
so all `F` commute, and by 1 all `E_a(λ)` commute. The two-sided variant expands `F(ω)` by its own
identity as well and runs the same induction on pairs.
