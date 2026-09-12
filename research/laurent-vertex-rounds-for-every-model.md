---
rg: 2
id: laurent-vertex-rounds-for-every-model
kind: claim
title: Every trace-preserving representation of the Theorem E actor rounds on the Laurent vertex EL_r(F_q[x^±1]) to genuine representations
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1), rounding on the polynomial vertex EL_r(F_q[x_1..x_d]); this rounds on the larger Laurent vertex EL_r(F_q[x^±1]), whose genuine representations restrict to unit type with no rate.
  theorem-e-vertex-rounds-to-unit-type-representations: that is unit-type rounding of the polynomial vertex; this is a rounding statement for a different Kazhdan subgroup that implies it exactly, with P_n = 1.
  kt-wreath-relative-canonical-actor-exactification: that rounds the whole actor, including SL_d(Z), on canonical wreath microstates; this rounds only the normal Laurent vertex, for every trace-preserving model.
  vertex-rounding-with-log-depth-rate: that is polynomial-vertex rounding with a quantitative defect condition; this is Laurent-vertex rounding, which needs no rate.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**OPEN.** Let `Δ = EL_r(F_q[x_1^(±1)..x_d^(±1)]) < G = Δ ⋊ SL_d(Z)`, with `r, d >= 3`, and fix a finite
generating set `F_Δ`. For every trace-preserving `σ : G -> U(prod_U M_n)`, after `o(n)` padding there should be
genuine representations `ρ_n : Δ -> U(n')`, with `n'/n -> 1`, such that

```text
max_(s ∈ F_Δ) ||σ_n(s) - ρ_n(s)||_2  ->  0     along U.
```

**Payoff.** Restricting `ρ_n` to `Γ = EL_r(F_q[x_1..x_d])` gives a unit-type rounding with `P_n = 1` exactly
(route `unit-type-rounding-via-laurent-vertex-rounding`). No compressor transport, torus bound or rate is needed.

## Attempts

- **Strict stability.** Impossible. `Δ` is infinite, residually finite and Kazhdan (Ershov–Jaikin-Zapirain),
  so Becker–Lubotzky (arXiv:1809.00632, abstract) applies. This claim is flexible, and flexible HS stability of
  higher-rank Kazhdan groups is open.
- **Robust spectral gap.** Insufficient, for the same reason as for `Γ` in
  `hs-stable-vertex-rounding-for-every-model`: `(T;FD)_rob` supplies no genuine representation.
- **Deduce it from polynomial-vertex rounding.** Reduced to `d` commutation conditions. Not closed.
  - The opposite implication holds. By `log-depth-rate-rounding-via-laurent-vertex-rounding`, this claim implies
    `vertex-rounding-with-log-depth-rate`, so it is at least as strong as input 1.
  - A unit-type rounding of `Γ` extends along `L -> A_u` only to `St_r(L)`.
  - By `laurent-extension-agrees-iff-inverse-defects-commute`, that extension agrees with `σ` on `St_r(L)` exactly
    when the `d` defects `W_i = ρ'(x_23(x_i^(-1)))^* σ(e_23(x_i^(-1)))` commute with `π(Γ)`.
  - Each `W_i` commutes unconditionally with `π(H_i)`, and `π_n(H_i) = π_n(Γ)` at every finite level. The gap is
    rigidity of ultraproduct commutants.
  - Under a regular trace the inverse `x_i^(m_n - 1)` has unbounded degree, so commuting with each fixed element
    of `H_i` gives no control. This is the same high-degree mechanism the log-depth rate targets.
  - Descent from `St_r(L)` to `Δ` also stays open: the symbols `{x_i, x_j}` can have unbounded order in `K_2(A_n)`.
- **Restrict to wreath models.** It pays only through lamp covariance.
  - Regular trace and a trace-zero symmetry in the vertex commutant can be added to any model by tensoring with
    finite-quotient models and `1_2`, without changing the root spectra of a rounding.
  - See artifact §5.
- **Enlarge the centralized subgroup, then reduce to one property (T) question (lane `nh-laurent-commutant`).**
  The `H_i` obstruction above is not fatal: the defect `W_i` centralizes far more than `H_i`, and the correct
  larger group has finite abelianization.
  - **Full off-corner commutation (Steinberg calculus, rigorous).** For `W_i = ρ'(x_23(x_i^(-1)))^* σ(e_23(x_i^(-1)))`,
    conjugation by `e_23(x_i^(-1))` is trivial on any root `(c,d)` with `c ≠ 3` and `d ≠ 2`, and on `(2,3)` itself.
    So `W_i` commutes **exactly in M** with the FULL root groups `π(e_cd(R_+))` for every `(c,d)` with `c ≠ 3, d ≠ 2`,
    and with the full `π(e_23(R_+))` — not merely with `e_cd(x_i R_+)`. Only the transpose-support of the defect root
    stays confined: row 3 `(3,k)` and column 2 `(k,2)` sit at level `(x_i)` (via `[e_23(x_i^(-1)), e_3k(x_i a)] = e_2k(a)`
    etc.), and the corner `(3,2)` at level `(x_i^2)`.
  - **Define `K_i`** = the mixed-level root-graded subgroup with `X_α = R_+` for `α` off row 3 / column 2 (and `α=(2,3)`),
    `X_α = (x_i)` for `α ∈ {(3,k),(k,2): k ∉ {2,3}}`, and `X_{(3,2)} = (x_i^2)`. It is closed under the Steinberg
    commutators (`[X_{(3,k)},X_{(k,2)}] = e_32((x_i^2)) = X_{(3,2)}`), `W_i` centralizes it, and `π_n(K_i) = π_n(Γ)`
    at every finite level (since `x_i` is a unit in `A_n`).
  - **`H_i` fails (T); this is exactly the recorded gap.** Reduce `mod (x_i^2)`: the ideal `(x_i)` becomes the
    square-zero ideal `J = (x_i)/(x_i^2) ≅ R_+/(x_i)`, and `⟨e_α(J)⟩` is ABELIAN and infinite. So `H_i` (ideal-only,
    `(x_i)` non-idempotent) has an infinite abelian quotient, hence no property (T). No fixed-generator spectral-gap
    argument over `H_i` can bridge the unbounded-degree `x_i^(m_n-1)`.
  - **`K_i` has FINITE abelianization for `r ≥ 4`.** Using a third index `l ∉ {2,3,k}`, every confined direction is a
    single commutator of `K_i` generators: `e_3k(x_i a) = [e_3l(x_i a), e_lk(1)]`, `e_k2(x_i a) = [e_kl(1), e_l2(x_i a)]`,
    `e_32(x_i^2 a) = [e_31(x_i a), e_12(x_i b)]`. So all `(x_i)`- and `(x_i^2)`-level directions die in `K_i^{ab}`, and the
    full-ring part is elementary of rank `≥ 2` (finite abelianization). The infinite-abelianization obstruction that kills
    `H_i` is DEFEATED by the extra full commutation.
  - **Reduction (rigorous).** If `K_i` has property (T) with a fixed finite generating set, the Kazhdan projection applied
    to `Ad π_n|_{K_i}` gives `W_i ∈ ∏_U π_n(K_i)' = ∏_U π_n(Γ)' = π(Γ)' ∩ M` (the last equality is `Γ`'s own (T)). By
    `laurent-extension-agrees-iff-inverse-defects-commute` item 2 this yields `σ∘q = ρ'` on `St_r(L)`. So **the converse,
    hence Laurent = unit-type on `St_r(L)`, follows from property (T) of `K_i` (`r ≥ 4`).**
  - **Remaining crux: is `K_i` Kazhdan?** A relative-(T) question in the Ershov–Jaikin-Zapirain / EJZ-Kassabov
    "groups graded by root systems" framework. The ideal levels `(x_i), (x_i^2)` are non-idempotent (the enemy of
    relative (T)) but are commutator-generated from the full-ring root groups, which is the input their spectral criterion
    uses. Not settled here; if `K_i` is (T) the converse holds, and the `St_r(L) → Δ` / `K_2` descent above is the only
    remaining gap to the full Laurent claim.
