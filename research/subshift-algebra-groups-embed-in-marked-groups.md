---
rg: 2
id: subshift-algebra-groups-embed-in-marked-groups
kind: claim
title: Elementary groups over subshift crossed products embed the space of subshifts topologically in marked groups, and minimal subshifts of finite type are isolated
distinct_from:
  binary-subshifts-embed-in-three-marked-kazhdan-groups: that is the case Gamma = Z, binary alphabet, F_2, with three fixed matrix generators; this is every finitely generated Gamma, every alphabet and every F_q with the standard elementary marking, and it adds the isolation of minimal subshifts of finite type.
  marked-subshift-elementary-group-determines-language: that shows the marked group determines L(X) for minimal Z-subshifts; this proves continuity in both directions with explicit moduli over every finitely generated group, for all subshifts.
  minimal-free-sft-full-group-pattern-models-are-exact: that is the topological full group statement for validly coloured Z^d-sets; this is the elementary group over the crossed product ring, compared across all subshifts.
invalidates: [free-minimal-sft-el-sofic-via-subshift-marked-limits]
artifacts:
  - research/artifacts/sk-fp-sofic-b-z2-soficity-map-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Setting.**
- `Γ` is a finitely generated group with a finite symmetric generating set `Σ`, and `A` is a finite alphabet.
- `q` is a prime power and `n >= 3`.
- For a subshift `Y ⊆ A^Γ`, put `R_Y = LC(Y,F_q) ⋊ Γ`, `G_Y = EL_n(R_Y)` and `P_Y = G_Y/(G_Y ∩ F_q^x 1_n)`.
- The marking is `e_ij(s)` for `i ≠ j` and `s ∈ {u_σ : σ ∈ Σ} ∪ {χ_[y(e)=a] : a ∈ A}`, plus a generator of `F_q`
  when `q` is not prime.

**Theorem.**
1. For every pattern `p ∈ A^F` there is one group word `W_p`, independent of `Y`, with `W_p = e_12(χ_[p])`.
   So `W_p = 1` in `G_Y` or in `P_Y` iff `p ∉ L(Y)`. For `F ⊆ B(ρ)`, `|W_p| <= 3·2^(|F|(2ρ+1)-1)`.
2. The relations of length `<= r` of `G_Y` and of `P_Y` depend only on the `B(r)`-patterns of `Y`.
3. `Y ↦ (G_Y, marking)` and `Y ↦ (P_Y, marking)` are homeomorphisms of the compact space of subshifts
   (Hausdorff/pattern topology) onto closed subsets of the space of marked groups. `Y ⊆ Y'` iff there is a
   marked epimorphism `G_(Y') → G_Y`.
4. A minimal subshift is an isolated point of the space of subshifts iff it is of finite type. So for an
   infinite minimal SFT `Ω`, no marked groups `G_Y` or `P_Y` with `Y ≠ Ω` converge to `G_Ω` or `P_Ω`.
5. `G_X` is a marked limit of groups over finite subshifts iff `X` is a limit of finite subshifts. These groups
   are residually finite for `Γ = Z^d`. Every minimal `Z`-subshift is such a limit (the periodic-word models of
   the Pestov 9.1 note), and no infinite minimal SFT is.

For a free minimal `Z^2`-SFT `Ω`, `S_n(Ω) = P_Ω`, since the centre is scalar
(`free-minimal-subshift-elementary-groups-are-simple-kazhdan`). So soficity of `S_n(Ω)` cannot come from
marked approximation by groups over other subshifts, and every finite pattern model has to be a periodic
quantum tiling.

Route: `subshift-algebra-groups-embed-in-marked-groups-proof`. Artifact §§2–3.
