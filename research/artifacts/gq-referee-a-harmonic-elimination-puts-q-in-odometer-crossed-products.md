# Referee report (gq-referee-a, proof-gap lens): harmonic elimination puts Q in odometer crossed products

**Reviewed:** `harmonic-elimination-puts-q-in-odometer-crossed-products` and its route `-proof`
(lane gq-deep-adelic-1, f9dbfcd34), read on origin/main.

**Verdict: PASS.** No gaps found.

## The proof, step by step
- **Steps 1–2.** `f∘γ = u_γ^{-1} f u_γ` lies in `R`, and the `E_k` are integer polynomials in commuting
  elements, so they lie in `R` too. Evaluating at a point gives `(f∘γ)(x) = f_K(γy)`, because `π` is
  equivariant.
- **Step 3, normality.** Because `Γ_M` is normal, `Γ/Γ_M` is a group and `(γy)_M = (γΓ_M)·y_M`. Right
  multiplication by `y_M` is a bijection, so `γ ↦ (γy)_M` is a bijection from `T_M` onto `Γ/Γ_M`.
  Exactly one `γ_0` hits `(x_∞)_M`.
- **Step 4.**
  - Agreement of `y` with `x_∞` at level `n` implies agreement at every lower level. So for `γ ≠ γ_0`,
    `ℓ(γy) = ℓ(c) < M` is a function of `c` alone.
  - Hence the multiset `V_M` does not depend on `x`.
  - `Π V_M = 1/D_M` and `Σ_{v ∈ V_M} 1/v = S_M`.
- **Step 5, the wild value.** Let `t` be the one value not in `V_M`.
  - `E_d = t/D_M`.
  - `E_{d−1} = 1/D_M + t·S_M/D_M`. The omit-one sum works for multisets with repeated values.
  - So `E_{d−1} − S_M E_d` is the constant `1/D_M`.
- **Step 6, strictness.**
  - Take `g ∈ Γ_j ∖ Γ_{j+1}`. The coset `c = x·g·Γ_M`, where `(x_∞)_M = xΓ_M`, agrees with `x_∞` modulo
    `Γ_j` but not modulo `Γ_{j+1}`.
  - So `m_j ≥ 1` for every `j < M`, and `M! | D_M`.
- **Step 7.** So `1/m ∈ R` for every `m ≤ M`, and hence `Q ⊆ R`.

## Setting and consequence
- **Continuity of `f_K`.** `ℓ` is locally constant off `x_∞`, and `f_K → 0` at `x_∞`. So `f_K` is continuous
  for the real topology on `Q`, which the node specifies.
- **The `SL_3(Z)` consequence.** Here `Γ_0 = Γ(1) = Γ`. The chain `Γ((n+1)!)` is strictly decreasing. Strong
  approximation makes `SL_3(Z) → SL_3(Z/m)` surjective, so `K = SL_3(Ẑ)`.
