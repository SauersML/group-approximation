---
rg: 2
id: fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
kind: claim
title: Every finitely generated group embeds in an infinite finitely generated simple Kazhdan group whose word problem has the same Turing degree
distinct_from:
  lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree: that needs the input to be LEF and gives an LEF host through the half-line overgroup; this uses the same half-line overgroup, drops every approximation hypothesis on the input and gives up only the LEF property of the host.
  lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts: that is the LEF equivalence with solvable word problem; this gives decidable simple Kazhdan hosts to every decidable input, LEF or not.
  erf-groups-have-decidable-simple-kazhdan-hosts: that covers effectively residually finite inputs; this covers all finitely generated inputs.
  lamplighter-bernoulli-crossed-products-simple-kazhdan-lef: that is the host for LEF acting groups with the LEF conclusion; this is the same host for every infinite finitely generated acting group, over the half-line overgroup, with no LEF conclusion.
  countable-group-embeds-in-fg-simple-kazhdan-group: that embeds every countable group in a simple Kazhdan group through small cancellation with no word problem control; this controls the Turing degree of the word problem.
  boone-higman-thompson-simple-envelope: that gives a decidable simple envelope that may split as an amalgam; this gives a decidable simple envelope with property (T), hence property FA.
  decidable-groups-embed-in-decidable-simple-fa-groups: that asks only for property FA and solvable word problem; this gives property (T) and the exact Turing degree for every finitely generated input.
artifacts: [research/artifacts/lamplighter-kazhdan-host-without-lef-2026-09-17.md]
---

**ESTABLISHED** through `fg-groups-simple-kazhdan-hosts-lamplighter-proof`.

Let `Γ` be a finitely generated group and `Δ = C(Γ)` its half-line overgroup
(`groups-embed-in-derived-subgroup-of-half-line-overgroup`). Put
`L = Z/2 ≀ Δ`, acting on `2^Δ` by shifts and finite flips, `R = LC(2^Δ, F_2) ⋊ L`
and `H = EL_3(R)`. Then:

1. `H` is an infinite, finitely generated, simple group with property (T), hence
   with property FA;
2. `γ ↦ diag(u_(δ_0(γ)), 1, 1)` embeds `Γ` in `H`, since `δ_0(Γ) ≤ [Δ,Δ] ≤ [L,L]`;
3. `WP(Γ) ≤_m WP(H) ≤_T WP(Γ)`.

In particular every finitely generated group with solvable word problem embeds
in an infinite finitely generated simple Kazhdan group with solvable word
problem.

## Why this matters

- It settles `decidable-groups-embed-in-decidable-simple-fa-groups`, the last
  missing prerequisite of part (D) of
  `finitary-permanence-closures-collapse-boone-higman-to-base`, and one of the
  two prerequisites of the route `boone-higman-from-simple-fa-inputs`.
- It makes Boone--Higman equivalent to its restriction to simple Kazhdan
  decidable inputs (`boone-higman-iff-simple-kazhdan-decidable-inputs`).
- It kills, for every decidable input, the class of permanence reductions
  mixing tree steps with infinitary steps
  (`mixed-permanence-closures-collapse-boone-higman-to-base`).

**The missing step, and why it was missed.** The LEF host was proved with the
hypothesis LEF throughout, but LEF is used only to prove that the host is LEF.
Minimality, topological freeness, ring simplicity, Steinberg simplicity of `EL_3`,
Ershov--Jaikin-Zapirain (T) and the word problem reduction need only an infinite
finitely generated acting group. The half-line overgroup was needed there to put
the input into a derived subgroup, because the host embeds only `[L,L]`. That
second use survives: `diag(u_γ, u_γ^(-1), 1)` is not a homomorphism for
non-abelian `Γ` (`shift-unit-of-subshift-crossed-product-is-not-elementary`), and
`diag(u_γ,1,1)` is elementary only when `[u_γ] = 0` in `K_1(R)`
(`perfect-groups-embed-in-crossed-product-elementary-groups`). But `C(Γ)` has
`WP(C(Γ)) ≡_T WP(Γ)` for every finitely generated `Γ`, LEF or not
(`half-line-overgroup-keeps-lef-and-solvable-word-problem`, item 2), so the
overgroup costs nothing here.

**Credit.** Without (T), the decidable case is classical: Boone--Higman (1974)
and Thompson (1980) embed every finitely generated group with solvable word
problem in a finitely generated simple group with solvable word problem. The
host here is the lamplighter host of
`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`, read without LEF.

## Attempts

1. **Reread the lamplighter host without LEF (2026-09-17).** See the artifact. *Settles the claim*, after the
   referee repair below.

**Referee (ref-01, 2026-09-17): REPAIRABLE, repaired.** The first version took `Δ = Γ × Z` and embedded `Γ` by
`γ ↦ diag(u_γ, u_γ^(-1), 1)`. That map is not a homomorphism for non-abelian `Γ`: the `(2,2)` entries give
`u_γ^(-1) u_η^(-1) = u_(γ^(-1)η^(-1))` against `u_((γη)^(-1)) = u_(η^(-1)γ^(-1))`, and `u` is injective. This is the
firewall of `shift-unit-of-subshift-crossed-product-is-not-elementary`. Repair: `Δ = C(Γ)`, `Γ ≅ δ_0(Γ) ≤ [Δ,Δ]`,
and `ℓ ↦ diag(u_ℓ,1,1)` on `[L,L]` (`perfect-groups-embed-in-crossed-product-elementary-groups`, item 3);
`WP(C(Γ)) ≡_T WP(Γ)` holds without LEF (the levelwise normal form of
`half-line-overgroup-keeps-lef-and-solvable-word-problem-proof` never uses it). Checked and unchanged: Lemmas 1-2 of the
2026-09-13 artifact use only `Δ` infinite and finitely generated; ring generation and finite generation of `EL_3(R)`;
EJZ (T) with its true hypothesis (finitely generated associative ring with 1, `n ≥ 3`); the Steinberg simplicity
hypotheses (ample, Hausdorff, compact infinite unit space, minimal, effective) and `Z(R) = F_2`; the subshift model and
`L(X) ≤_T WP(Δ)`; FA through Watatani. A bounded literature search found no prior simple Kazhdan statement with
word problem control.
