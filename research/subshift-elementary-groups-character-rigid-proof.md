---
rg: 2
id: subshift-elementary-groups-character-rigid-proof
kind: route
title: The trivial weight is central, and a Bessel inequality over far-apart root commutators forces the rest to be regular
target: subshift-elementary-groups-are-character-rigid
requires: [subshift-tower-unit-group-characters-are-constant]
artifacts:
  - research/artifacts/sk-characters-rigidity-b-proof-2026-09-13-part1.md
  - research/artifacts/sk-characters-rigidity-b-proof-2026-09-13-part2.md
---

Proves the stronger statement: every character of `G = EL_3(LC(X,F_2) ⋊ Z)`, for `X` an infinite minimal Cantor system, is `c·1 + (1−c)δ_e`. The full text is in part 2, §4–§6.

1. **Central trivial part.**
   - Take the GNS data `(π, L²(M,τ), ξ)`. Let `p_K` be the projection onto the `K`-fixed vectors, for a locally finite `K` exhausted by finite subgroups.
   - By the required claim, `χ = c` on `L_y ∖ 1`, so `τ(p_{L_y}) = c`. The same holds for the root subgroup `A = e_12(LC(X,F_2)) ⊆ L_y`: `τ(p_A) = c`.
   - `p_{L_y} ≤ p_A`, and the trace is faithful, so `p_{L_y} = p_A = p_{L_{y'}}`.
   - Generation gives `π(x)p_A = p_A` for all `x ∈ G`, so `p_A` is central.
   - Hence `χ = c + (1−c)χ_2`, where `χ_2 = τ((1−p_A)π(·))/(1−c)` vanishes on every `L_y ∖ 1`.
2. **Bessel step.** Let `ψ` be a character vanishing on every `L_y ∖ 1`, and let `g ≠ 1`.
   - Choose `K` small clopen sets `V_k` for `g`, as in the note's simplicity proof, with pairwise disjoint towers and roots `x_k = e_{i_kj_k}(e_{V_k})` that do not commute with `g`.
   - Such sets exist because nontriviality of `g` over a small set is inherited by its clopen subsets.
   - Conjugation by `g` maps `x_k` into the finite tower group `H_{V_k}`. So `g^{-1}x_lx_k g·x_lx_k` is a nontrivial element of `H_{V_l}H_{V_k} ⊆ L_{y*}`, for `y*` outside the towers.
   - So the vectors `π(x_kgx_k^{-1})ξ` are orthonormal, and each has inner product `ψ(g)` with `ξ`.
   - Bessel's inequality gives `K|ψ(g)|² ≤ 1`, so `ψ = δ_e`.

**Model tests** (part 2 §8):
- periodic `X` fails the hypothesis, and its congruence characters show the conclusion fails;
- non-minimal `X` fails it too, and subsystem quotients give non-regular characters;
- the Dudko–Medynets characters of `[[T]]'` fail the analogue of the decay step.
