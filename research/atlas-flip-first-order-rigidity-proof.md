---
rg: 2
id: atlas-flip-first-order-rigidity-proof
kind: route
title: Two-sided translation calculus at the flip, closed by a two-case identity
target: atlas-flip-first-order-rigidity
requires: [atlas-steinberg-rank-five-translation, atlas-true-criterion-baseline]
artifacts:
  - research/artifacts/atlas-flip-stationarity-2026-08-17.json
  - experiments/atlas_flip_stationarity_exact.py
---

# Two-sided translation calculus at the flip, closed by a two-case identity

Work at `k = 1`; the general case follows at the end by tensoring.  At
`W = I` (i.e. `U = J`) a first-chart letter `g` of a `T_St` word acts as
the left translation `L_g` on `ℂ[A₈]` and a second-chart letter `h` as
the right translation `R_h` (convention `R_h R_b = R_{hb}`; the flip is
what assigns the charts to opposite sides, and the assignment is
validated by the exact baseline: control defects identically zero,
active defects exactly `2` — `atlas-true-criterion-baseline`).

**1. The differential is a signed sum of two-sided translations.**  For
`W_t = e^{tX}` the second-chart letters move by `W_t R_h W_t*`, so for a
word `w = s_1 ⋯ s_m`,

```text
d/dt|₀ tr π_{W_t·J}(w) = Σ_j tr(C_j [X, R_{h_j}] D_j) = Σ_j tr(M_j X),
M_j = [R_{h_j}, D_j C_j],
```

the sum over second-chart positions `j`, with `C_j = s_1⋯s_{j−1}` and
`D_j = s_{j+1}⋯s_m` evaluated at `t = 0` — both of the form `L_ℓ R_r`
since left and right translations commute.  Writing `ℓ_j, r_j` for the
prefix products of first- and second-chart letters and `λ_j, ρ_j` for
the suffix products,

```text
M_j = L_{a_j}(R_{h_j b_j} − R_{b_j h_j}),   a_j = λ_j ℓ_j,   b_j = ρ_j r_j.
```

**2. Every term is a pair of conjugates of the factor projections.**
With `p₁ = ℓ_j λ_j` (no second-chart letter interrupts the first-factor
product) and `p₂ = r_j h_j ρ_j`:

```text
a_j = λ_j p₁ λ_j⁻¹,    h_j b_j = r_j⁻¹ p₂ r_j,    b_j h_j = ρ_j p₂ ρ_j⁻¹.
```

**3. Case `p₂ = I`: site-by-site death.**  `r_j h_j ρ_j = I` gives
`b_j = ρ_j r_j = h_j⁻¹`, so `R_{h_j b_j} − R_{b_j h_j} = R_I − R_I = 0`
at every site separately.  This covers the 4,564 doubly trivial words
and the 36 first-factor escapees.

**4. Case `p₁ = I`: cyclic telescope.**  Then `a_j = I` for every `j`,
so all terms live in the right-translation algebra.  Let
`j_1 < ⋯ < j_t` be the second-chart positions.  Since
`r_{j_{i+1}} = r_{j_i} h_{j_i}` and `ρ_{j_i} = h_{j_i}⁻¹ r_{j_i}⁻¹ p₂`,

```text
b_{j_i} h_{j_i} = ρ_{j_i} p₂ ρ_{j_i}⁻¹ = r_{j_{i+1}}⁻¹ p₂ r_{j_{i+1}} = h_{j_{i+1}} b_{j_{i+1}},
```

so the `−` term at `j_i` cancels the `+` term at `j_{i+1}`, cyclically:
`r_{j_1} = I` and `ρ_{j_t} = I` make both boundary terms `R_{p₂}`.  The
signed sum telescopes to zero.  This covers the 36 second-factor
escapees.

**5. The dichotomy is total.**  Machine classification of the full list
(`atlas-rank5-T_St.json`, 4,636 words): 4,564 with both projections
trivial, 36 with only `p₁ ≠ I`, 36 with only `p₂ ≠ I`, **zero with
both nontrivial** — so cases 3 and 4 exhaust `T_St` and the theorem
holds per word.  (For a word escaping in both factors the argument
genuinely fails — a three-block interleaved word generically has
surviving terms — so the single-factor-escape hypothesis is the load-
bearing fact, not an artifact of the calculus.)

**6. Multiplicity.**  At `U₀ = J ⊗ V`, `V ∈ U(k)`, second-chart letters
act by `(I ⊗ V)(R_h ⊗ I_k)(I ⊗ V)* = R_h ⊗ I_k`, so every operator
above tensors with `I_k` and each per-word sum is `0 ⊗ I_k = 0`.
First-order rigidity holds in all of `U(20160·k)` for every `k` and at
every point of the flip manifold.

**7. Machine verification (exact, integer, independent of 3–4).**
`experiments/atlas_flip_stationarity_exact.py` computes the
unsymmetrized differential `M = Σ_{w,j} ±(a, c)` as an integer-weighted
multiset of pairs in `A₈ × A₈` (distinct pairs are distinct operators —
trivial center), antisymmetrizes under `(a,c) ↦ (a⁻¹,c⁻¹)`, and
evaluates `‖M − Mᵀ‖²_HS` exactly via fixed-point counts
`tr(P_{(a,c)}ᵀ P_{(a',c')}) = |C(u)|·[u ∼ v]`, `u = a⁻¹a'`,
`v = c⁻¹c'`, with conjugacy decided by the complete Frobenius invariant
(ranks of `f(u)^j` over the eight irreducible `𝔽₂`-polynomials of
degree ≤ 4) — no floating point anywhere.  Output
(`research/artifacts/atlas-flip-stationarity-2026-08-17.json`, sioux
acn116, 2026-08-17): active slice 376 raw terms, `0` surviving pairs in
`M` itself (stronger than gradient vanishing); control slice `0` raw
terms; combined `‖M − Mᵀ‖² = 0` exactly.  A per-word rerun confirms all
72 active words cancel individually.  Oracle self-check: exactly 14
conjugacy classes over 20160 elements, the true count for
`GL₄(𝔽₂) ≅ A₈`.  Engine sanity: hand-checked on three word shapes —
all-second-chart words cancel by trace conjugation-invariance, a
two-letter mixed word vanishes by `[L, R] = 0`, and a three-block
interleaved word with both projections nontrivial does NOT cancel, so
the verdict is not an artifact of the term generator.
