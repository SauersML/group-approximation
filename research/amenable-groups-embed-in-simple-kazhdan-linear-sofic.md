---
rg: 2
id: amenable-groups-embed-in-simple-kazhdan-linear-sofic
kind: claim
title: Every finitely generated amenable group embeds in an infinite simple Kazhdan linear sofic group
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that embeds residually finite groups in LEF envelopes through Toeplitz subshifts with exact finite models; this embeds amenable groups, which need not be residually finite or LEF, in envelopes that are only linear sofic, through Folner rank models.
  simple-kazhdan-linear-sofic-non-lef-group-exists: that is the existence of one simple Kazhdan linear sofic group that is not LEF; this is a universal embedding statement covering every finitely generated amenable group.
---

**OPEN** (status restated by sk-verify-4, 2026-09-13). The route `amenable-groups-embed-in-simple-kazhdan-linear-sofic-proof` requires `double-swap-embeds-group-in-derived-subgroup`, which is refuted, so it does not fire. The perfect case is `amenable-perfect-groups-embed-in-kazhdan-linear-sofic`. The statement under consideration: Let `Γ` be a finitely generated amenable group and `q` a prime power.
There is an infinite, finitely generated, simple group `S` with property (T) that is `F_q`-linear
sofic and contains an isomorphic copy of `Γ`. One may take

    S = EL_3(LC(X, F_q) ⋊ Δ) / Z,   Δ = (Γ × Γ) ⋊ C_2,

with `X ⊆ A^Δ` any free minimal subshift, and the same holds for `EL_n`, `n >= 3`.

**Why it is worth stating.** Amenable groups need not be LEF: a finitely presented LEF group is
residually finite (Vershik--Gordon), and there are finitely presented solvable groups that are not
residually finite. So the envelopes here cannot be LEF, and this is the amenable half of
`sofic-groups-embed-in-simple-kazhdan-sofic-groups`, with the Hamming metric weakened to the rank
metric. The obstruction to strengthening it is
`gap-sofic-approximations-are-local-embeddings`: models of `EL_n` inside `GL_N(F_q)` acting on
vectors convert a rank defect into a Hamming defect `1 - q^(-O(r))`, so they carry LEF or nothing.

**Inputs.** The embedding step is `double-swap-embeds-group-in-derived-subgroup`; the rank model is
`amenable-minimal-crossed-products-have-faithful-rank-models`; simplicity is
`steinberg-elementary-groups-are-simple-mod-centre`; property (T) is
`elementary-groups-over-fg-rings-have-property-t`; linear soficity of the projective elementary group
is `rank-modelled-simple-rings-give-linear-sofic-projective-el`. Free minimal subshifts over an
arbitrary countably infinite group are Gao--Jackson--Seward.

**Credit.** Kionke--Schesler embed every finitely generated residually finite group in a finitely
generated simple LEF group, without property (T). Bounded novelty check: a grep of this graph on
2026-09-13 and one web search on Gao--Jackson--Seward; no literature search for universal embeddings
into simple Kazhdan groups was performed by this lane.

Route: `amenable-groups-embed-in-simple-kazhdan-linear-sofic-proof`.

## Attempts

- **Swap double (dies).** `γ ↦ (γ,γ^(-1))` into `(Γ×Γ)⋊C_2` is multiplicative only for abelian `Γ`, and no permutational wreath product puts a non-perfect `Γ` into its derived subgroup (`wreath-products-keep-the-abelianization-of-the-base`). The embedding step needs a finitely generated amenable overgroup `Δ ⊇ Γ` with `Γ ≤ [Δ,Δ]`, or a `K_1`-invisible copy (`perfect-groups-embed-in-crossed-product-elementary-groups`). The Ore overgroup needs residual finiteness.

**Review (sk-verify-4, 2026-09-13): route does not fire.** Steps 1 and 7 use the refuted swap double; steps 2–6 were not re-reviewed. See `research/artifacts/sk-review-4-2026-09-13-part4.md` §1.
