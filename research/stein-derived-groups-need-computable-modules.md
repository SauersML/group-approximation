---
rg: 2
id: stein-derived-groups-need-computable-modules
kind: claim
title: If the derived Stein group D(V(Γ,Λ,ℓ)) has solvable word problem on its finitely generated subgroups, every ratio γ/ℓ with γ in Γ is a computable real; so irrational-slope Thompson groups with noncomputable slope have 2-generated simple derived subgroups with unsolvable word problem
distinct_from:
  full-group-word-problem-iff-recursive-language: that is the Grigorchuk--Medynets theorem for derived full groups of minimal subshifts; this transports it into Stein's piecewise-linear groups through their interval exchange subgroups.
  every-turing-degree-is-a-simple-kazhdan-lef-word-problem: that realizes every Turing degree by simple Kazhdan LEF groups over Sturmian subshifts; this uses the same Sturmian angle-to-language step to constrain which Stein groups can have solvable word problem.
  fp-simple-groups-have-no-interval-exchange-action: that says a finitely presented infinite simple group has no nontrivial action by interval exchanges; this is about Stein groups, which contain interval exchange groups as subgroups but do not act by interval exchanges.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (route `stein-derived-groups-need-computable-modules-proof`; lane proof, not reviewed; no
priority claimed).

## Setting (Stein; Tanner, arXiv:2312.07375, Definition "Stein's Groups")

`Λ` is a subgroup of `(R_{>0}, ·)`, `Γ ⊆ R` is a `Z·Λ`-submodule with `ΛΓ = Γ`, and `ℓ ∈ Γ`, `ℓ > 0`.
`V(Γ,Λ,ℓ)` is the group of right-continuous piecewise-linear bijections of `[0,ℓ)` with slopes in `Λ` and
finitely many breakpoints and discontinuities in `Γ`. `D(·)` is the derived subgroup. Tanner proves
(Theorem `fg when fg by alg`): `D(V(Γ,Λ,ℓ))` is simple for all such data, and it is finitely generated,
indeed 2-generated, iff `Γ ⋊ Λ` is finitely generated.

## Statement

1. **Computability obstruction.** Suppose every finitely generated subgroup of `D(V(Γ,Λ,ℓ))` has solvable
   word problem. This holds, for instance, if `D(V(Γ,Λ,ℓ))` is finitely presented, or embeds in a finitely
   presented simple group (`simple-envelope-forces-solvable-word-problem`). Then every element of `ℓ^{-1}Γ`
   is a computable real. In particular every slope `λ ∈ Λ` is computable, since `λ = (λℓ)/ℓ`.
2. **Irrational-slope Thompson groups.** Let `λ ∈ (0,1)` be a noncomputable real, and put
   `V_λ = V(Z[λ,λ^{-1}], ⟨λ⟩, 1)`. Then `D(V_λ)` is an infinite 2-generated simple group with unsolvable word
   problem. So it is not finitely presented, and it embeds in no finitely presented simple group. All but
   countably many `λ ∈ (0,1)` are noncomputable.

## Consequences

- **Tanner's question.** Tanner (loc. cit., Question after the finite generation theorem) asks: under what
  conditions is `D(V(Γ,Λ,ℓ))` finitely presented? Item 1 gives a necessary condition: `ℓ^{-1}Γ` must consist
  of computable reals. It is independent of how `Γ` and `Λ` are generated.
- **Transcendental slopes, remark.** Tanner's rational homology computation states
  `H_*(D(V_λ); Q) ≅ ⊕_{i≥1} Q` for `* > 1` when `λ` is transcendental. If that is correct, `D(V_λ)` is never
  finitely presented for transcendental `λ`, because `H_2` of a finitely presented group is finitely
  generated. Item 2 adds, for noncomputable `λ`, that `D(V_λ)` does not even embed in a finitely presented
  simple group. For computable transcendental `λ` the question is open:
  `transcendental-slope-thompson-groups-satisfy-boone-higman`.
- **Boone--Higman.** These groups are Thompson-like f.g. simple groups outside every Boone--Higman host, for
  the trivial reason that their word problem is unsolvable. The content is to locate that failure exactly:
  it is computability of the breakpoint module.
