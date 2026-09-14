---
rg: 2
id: whitehead-diagonal-map-is-not-multiplicative
kind: claim
title: The Whitehead diagonal map X to diag(X, X^-1) is multiplicative only on commuting pairs
invalidates:
  - char-p-linear-embedding-projective-leavitt-power-proof
  - crossed-product-group-projective-elementary-embedding-proof
  - simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow
  - rank-modelled-non-lef-el-via-amenable-non-rf-subflow
distinct_from:
  char-p-linear-groups-embed-in-projective-leavitt-power-e-groups: that is the embedding theorem whose proof used this map as a group embedding into E_m; this records that the map is not a homomorphism on any nonabelian group, so that proof does not land H in E_m.
artifacts:
  - research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md
---

**ESTABLISHED.** Let `R` be a ring and `X, Y in GL_N(R)`. Put
`w(X) = diag(X, X^-1)` in `GL_(2N)(R)`. Then `w(XY) = w(X) w(Y)` if and only
if `XY = YX`.

So for a nonabelian subgroup `H <= GL_N(R)`, the map `X |-> diag(X, X^-1, 1, ..., 1)`
is not a group homomorphism, and it embeds no nonabelian `H` as a subgroup.

**Consequence (bh-reviewer, 2026-09-12).** Theorem C of
`research/artifacts/boone-higman-char-p-all-degrees-2026-09-12.md` calls this map
"an injective homomorphism `H -> E_m(R_d)`". That step fails for every
nonabelian finitely generated linear group, for example `SL_3(F_p[t])`. So the
route `char-p-linear-embedding-projective-leavitt-power-proof` does not prove
its target. Its other steps stand:
- Lemma A: `H <= GL_N(R_d)`;
- Lemma B: each single `diag(X, X^-1)` lies in `E_(2N)(R_d)`;
- the centre calculation.
What is missing is a homomorphic embedding into `E_m`. The known candidates
need `K_1`-type information; see `## Attempts` on
`char-p-linear-groups-embed-in-projective-leavitt-power-e-groups`.

**Consequence (sk-subgroups, 2026-09-13).** `crossed-product-group-embeds-in-projective-elementary-group`
asserted that `g |-> diag(θ(g), θ(g)^-1, 1_(N-2))` is an injective homomorphism `Γ -> EL_N(R)` for every
injective `θ : Γ -> R^×`. That fails whenever `Γ` is nonabelian.
- **Witness in every topological full group.** Take a clopen `U` with `U, TU, T^2U` disjoint.
  - The level swaps `σ` (`T` on `U`, `T^-1` on `TU`) and `τ` (`T` on `TU`, `T^-1` on `T^2U`) do not commute, since `στ(U) = TU` while `τσ(U) = T^2U`.
  - So their full-group units do not commute.
- **Invalidated routes.**
  - `crossed-product-group-projective-elementary-embedding-proof`: its step 2, "ι is a homomorphism", fails.
  - `simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow` and `rank-modelled-non-lef-el-via-amenable-non-rf-subflow`: both apply the map to the nonabelian Abels–Prüfer group `Γ_p`.
- **What survives.**
  - For abelian images the map is a homomorphism.
  - `diag(θ(g), 1, ..., 1)` is a homomorphism, and on `[Γ,Γ]` it lands in `E_N(R)`, because
    `diag(aba^-1b^-1, 1) = diag(a,a^-1) diag(b,b^-1) diag((ba)^-1, ba)`.
  - Non-LEF for `N >= 4` passes through the ring: `lef-elementary-groups-force-lef-rings`,
    `simple-lef-rings-are-exactly-matricial`, `exactly-matricial-rings-have-lef-general-linear-groups`.
  - The repaired routes are `simple-kazhdan-linear-sofic-non-lef-via-lef-converse` and `rank-modelled-non-lef-el-via-lef-converse`.
  - Rank `N = 3` is open.
- Details: `research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md` §4.
