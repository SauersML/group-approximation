---
rg: 2
id: dyadic-tower-subshift-full-group-non-uniform-growth-proof
kind: route
title: The dyadic small-ball engine run on abstract constant dyadic towers with a bounded generating partition of the induced system
target: dyadic-tower-subshift-full-group-non-uniform-growth
requires:
  - derived-full-group-generated-by-good-three-cycles
  - minimal-subshift-derived-full-group-exponential-growth
  - sauer-schesler-grigorchuk-level-estimates
artifacts:
  - research/artifacts/sk-sturmian-growth-plan-2026-09-14.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part2.md
---

This is the derivation of `dyadic-substitution-derived-full-groups-non-uniform-growth-proof` (artifacts parts 1–2, reviewed twice), with the substitution replaced by the hypotheses. The only changes:

1. **Tower model** (part 1 §2). For a good scale `m = n+3` (infinitely many, `n ≥ 5`), take `V = V_m` and `S = S_m` from (H1).
   - Every point is `T^(β(y))v` with `v ∈ V`, `y ∈ Y_n = {0,1}^n × {1,…,8}`.
   - `T` moves levels by one and applies `S` at the top.
   - Uniform level permutations, partial level permutations, shift pairs `[s_y, L_(y y′)]`, and the membership of their even parts in `[[T]]′` use only (H1).
2. **Local generators** (part 1 §3). `ζ_a` runs over `a ∈ 𝒫_m` from (H2), instead of the letter cylinders.
   - These are disjoint clopen sets covering `V`, so the `ζ_a` commute, and the type-4 group is `(Z/3)^(|𝒫_m|) × Z`.
   - `|T_n| = 20166 + |𝒫_m| ≤ 20166 + K`.
3. **Generation** (part 1 §4).
   - Step 1 is unchanged.
   - Step 2(b): the set `𝔅` of clopen `B ⊆ V` with `ζ_B ∈ W_n` contains every `a ∈ 𝒫_m`, and is closed under complements, intersections and `S^(±1)`. By (H2) it contains every clopen subset of `V`.
   - Step 2(c) and Step 3 use only (H1) (`2^m ≥ 32`) and `derived-full-group-generated-by-good-three-cycles`. So `W_n = [[T]]′`.
4. **Counting** (part 2 §§5–6). This is unchanged, with `|A|` replaced by `K`: `P_4(ℓ) ≤ (3^K(2ℓ+1))^(Cℓ^α)·exp(Cℓ^α)`. So `γ^(T_n)(ℓ) ≤ exp(Cℓ^β)` for `ℓ ≤ r_n/3`, with `C, β` depending only on `K`.
5. **Conclusion** (part 2 §7).
   - `ω([[T]]′) ≤ exp(C⌊r_n/3⌋^(β−1))` along the good scales, and `r_n → ∞`, so `ω = 1`.
   - Exponential growth comes from `minimal-subshift-derived-full-group-exponential-growth` (an infinite minimal subshift is not an odometer).
