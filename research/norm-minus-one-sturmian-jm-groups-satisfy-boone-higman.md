---
rg: 2
id: norm-minus-one-sturmian-jm-groups-satisfy-boone-higman
kind: claim
title: If the real quadratic field of an irrational angle α has a unit of norm −1, the Juschenko--Monod group of the Sturmian subshift of α embeds in the finitely presented simple derived subgroup of a metallic-mean Stein group
distinct_from:
  stein-derived-groups-need-computable-modules: that is the computability obstruction for Stein groups with noncomputable breakpoint modules; this is the positive embedding for quadratic angles, through Stein groups whose derived subgroup has finite index.
  computable-grigorchuk-groups-satisfy-boone-higman: that embeds computable Grigorchuk groups in finitely presented simple groups; this does it for derived full groups of quadratic Sturmian subshifts, which are amenable, simple and not finitely presented.
  fp-simple-groups-have-no-interval-exchange-action: that forbids finitely presented infinite simple groups from ACTING by interval exchanges; here the interval exchange group is a subgroup of the finitely presented simple host, which acts with nontrivial slopes.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (route `norm-minus-one-sturmian-jm-groups-satisfy-boone-higman-proof`; lane
proof, not reviewed). It rests on three cited inputs, none re-proved here:
- (C) type `F_∞` of `V(Z[ε],⟨ε⟩,ℓ)` for quadratic `ε`: Cleary, RMJM 25 (1995) and Illinois J. Math. 44
  (2000). This is read via Matui, arXiv:2412.05492, Remark on Stein's groups; Cleary's papers themselves were
  not obtained. Burillo--Nucinkis--Reeves (arXiv:2006.02401) state the golden case and say it follows by
  Stein's methods, without writing it out.
- (L) the groupoid homology `H_0 = Γ/(1−ε)Γ` and `H_k ≅ H_{k+1}(Γ ⋊ Λ)` for `k ≥ 1` (Li), and the AH exact
  sequence for `V(Γ,Λ,ℓ)` (Li, Corollary E), both as stated by Tanner, arXiv:2312.07375.
- (S) simplicity of `D(V(Γ,Λ,ℓ))`: Tanner, loc. cit.

## Statement

For `m ≥ 1` let `ε_m = (√(m²+4) − m)/2 ∈ (0,1)`, the root of `t² + mt − 1`, and put
`Γ_m = Z[ε_m] = Z[ε_m^{±1}]`.

1. **Hosts.** For every integer `N ≥ 1`, `D_{m,N} := D(V(Γ_m, ⟨ε_m⟩, N))` has index at most 4 in
   `V(Γ_m,⟨ε_m⟩,N)`. So it is a finitely presented (indeed `F_∞`) infinite simple group.
2. **Guests.** Let `K` be a real quadratic field containing a unit of norm −1, and `α ∈ K` irrational. Then
   `K = Q(ε_m)` for some `m ≥ 1`. The derived topological full group `G_α'` of the Sturmian subshift of angle
   `α` embeds in `D_{m,N}` for suitable `N`. `G_α' ≅ IE(Z+Zα)'` is an infinite, finitely generated, simple,
   amenable group (Matui; Juschenko--Monod).

So every such Juschenko--Monod group satisfies Boone--Higman. The fields covered are
`Q(√(m²+4))`: `Q(√5)`, `Q(√2)`, `Q(√13)`, `Q(√29)`, `Q(√10)`, `Q(√53)`, `Q(√17)`, ... These are exactly the real
quadratic fields with a unit of norm −1.

## Priority

The golden case `m = 1`, `α = τ` is Tanner's remark "Juschenko--Monod groups in Cleary's group"
(arXiv:2312.07375): `IE(Z ⊕ τZ) ↪ V_τ`, with `D(V_τ)` simple and finitely presented. What is added here:
- every `m`;
- every angle of the field, via rescaling;
- a proof that the derived subgroup has finite index, via (L).

No priority is claimed beyond that.

## Not covered

- **Quadratic fields whose units all have norm +1**, such as `Q(√3)`. For them `H_2(Γ⋊Λ) ⊇ Z`, so the derived
  subgroup has infinite index and its own finite presentation is open (Tanner's question). The Juschenko--Monod
  groups of these fields are nevertheless covered by `stein-v-groups-act-with-type-a-on-breakpoints` (09-18),
  with a twisted Brin--Thompson host.
- **Cubic and higher angles.**
- **Computable transcendental angles:** `transcendental-slope-thompson-groups-satisfy-boone-higman`.
