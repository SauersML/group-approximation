---
rg: 2
id: dyadic-substitution-derived-full-groups-non-uniform-growth-proof
kind: route
title: Small-ball generating sets of [[T]]′ from constant-height towers, Grigorchuk levels and commuting local 3-cycles
target: dyadic-substitution-derived-full-groups-non-uniform-growth
requires:
  - constant-length-substitution-tower-partition
  - derived-full-group-generated-by-good-three-cycles
  - minimal-subshift-derived-full-group-exponential-growth
  - sauer-schesler-grigorchuk-level-estimates
artifacts:
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part1.md
  - research/artifacts/sk-cornulier-q7-nonuniform-growth-2026-09-13-part2.md
---

The complete derivation is in the artifact parts 1–2. Outline:

1. **Tower model** (part 1 §2), via `constant-length-substitution-tower-partition` iterated.
   - For `m = n+3` and `N = 2^m`: `V = ζ^m(X)` is clopen, `X = ⊔_(i<N) T^iV`, `T^N V = V`, and `(V, S = T^N|V) ≅ (X,T)`.
   - Label the levels by `Y_n = {0,1}^n × {1,…,8}`.
   - The following lie in `[[T]]′`:
     - uniform level permutations `L_π`, for `π` even;
     - partial 3-cycles `ζ_B` over clopen `B ⊆ V`;
     - shift pairs `σ_(y,y′) = [s_y, L_(y y′)]`.
2. **Generators** (part 1 §3). `T_n` consists of:
   - truncated Grigorchuk generators acting diagonally on the 8 sheets;
   - `Alt(8)` on the fibre over `η_n`;
   - the double transposition linking `ρ_n, θ_n` on sheets 1,2;
   - `ζ_a` (a 3-cycle over the letter cylinder `U_a` on sheets 3,4,5 over `ρ_n`) and `σ_n` (`S` on sheet 6, `S^(−1)` on sheet 7 over `ρ_n`).

   `|T_n|` is bounded, and the type-4 group is `(Z/3)^|A| × Z`.
3. **W_n = [[T]]′** (part 1 §4).
   - `Alt(Y_n) ≤ W_n`: 3-cycles in fibres, the crossing 3-cycle from the linking involution, and connectivity (item 4 of the level estimates).
   - Inside one fibre, the set of `B` with `ζ_B ∈ W_n` contains the letter cylinders and is closed under complements, intersections (`[(1 2 3),(3 4 5)] = (1 4 3)` pointwise) and `S^(±1)` (conjugation by `σ_(1,4)σ_(2,5)σ_(3,6)`). So it is every clopen set.
   - Twisted 3-cycles come from conjugating by products of shift pairs on three spare sheets.
   - Every good `σ_U` is a product over levels of twisted 3-cycles on three consecutive levels. `Alt(Y_n)` moves those into one fibre.
   - `derived-full-group-generated-by-good-three-cycles` then gives `W_n = [[T]]′`.
4. **Counting** (part 2 §§5–6), as in Sauer–Schesler `lem:commuting-conjugates`, `lem:normal-form`, `lem:count-p1..p4`.
   - Conjugates of types 2, 3, 4 by words of length `≤ r_n` commute: separation (item 3) and disjoint sheets.
   - Normal form `p_1p_2p_3p_4`, with `p_2 ∈ ∏ Alt(8)` over an inverted orbit, `p_3` a permutation of an inverted orbit, and `p_4 ∈ ∏ (Z/3)^|A| × Z` with `Z`-coordinates in `[−ℓ,ℓ]`.
   - Items 1–2 of the level estimates give `γ(ℓ) ≤ exp(Cℓ^β)` for `ℓ ≤ r_n/3`.
5. **Conclusion** (part 2 §7). `ω([[T]]′) ≤ exp(C⌊r_n/3⌋^(β−1)) → 1`, and exponential growth holds by `minimal-subshift-derived-full-group-exponential-growth`.
