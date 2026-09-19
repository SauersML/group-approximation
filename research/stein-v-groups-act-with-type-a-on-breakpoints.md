---
rg: 2
id: stein-v-groups-act-with-type-a-on-breakpoints
kind: claim
title: A finitely presented Stein V-group whose shorter-interval versions are finitely generated acts with type (A) on its breakpoint set, so all its subgroups satisfy Boone--Higman; its quadratic (norm −1) instance is subsumed by the Pisot RSG route; norm +1 slopes are open (corrected 09-18)
distinct_from:
  quadratic-rotation-iet-groups-satisfy-boone-higman: that (bh-free-03, landed earlier on 09-18) already embeds IET(Z+αZ), α quadratic, in a finitely presented simple group, via the substitutive Sturmian coding and contracting rational similarity groups; the Sturmian corollary here is an independent route. What is new here is the type (A) action of the Stein V-group itself, which gives Boone--Higman for ALL subgroups of V(Z[λ],⟨λ⟩,ℓ), for example D(V_λ), F_λ, T_λ when λ has norm +1.
  circle-pl-groups-act-with-type-a-on-breakpoint-orbits: that treats the circle T-versions and needs A/(IP·A) finite for finitely many pair orbits; it leaves the V-versions open because V-point stabilizers are not interval groups. This proves finite generation of those stabilizers (an ascending union of shorter-interval V-groups, closed off by one germ contraction) and gets one pair orbit from interval exchanges, with no finiteness of A/(IP·A).
  norm-minus-one-sturmian-jm-groups-satisfy-boone-higman: that uses the finite-index derived subgroup of a metallic-mean Stein group as a finitely presented simple host, which needs a unit of norm −1; this passes through the twisted Brin--Thompson group instead and covers every real quadratic field.
  stein-derived-groups-need-computable-modules: that is the obstruction for noncomputable breakpoint modules; here the modules are algebraic.
artifacts:
  - research/artifacts/gq-bh-bh-near-actions-stein-slopes-reading.md
---

**ESTABLISHED** (route `stein-v-groups-act-with-type-a-on-breakpoints-proof`; lane proof, elementary, not
reviewed; no priority claimed).

**CORRECTION (09-18, Cleary read at source).** The earlier quadratic instance cited "(C) Cleary: `V(Z[λ],⟨λ⟩,ℓ)`
is `F_∞` for quadratic λ" via Matui's Remark. Cleary 1995 (RMJM 25, 935–955) and Cleary 2000 (Illinois J. Math. 44,
453–464) were read at source (gq/src/bh-near-actions/cleary/). They prove finite presentation and `FP_∞` only for
the F-versions `F(1, Z[λ], ⟨λ⟩)`, and only for `λ` with `1 = nλ + λ²` (Cleary 1995, p. 954: metallic means, norm
−1). Matui's paraphrase overstates this. The quadratic instance below is corrected accordingly: norm −1 slopes are
covered, with (F1) now from `pisot-unit-slope-stein-groups-are-finitely-presented`; norm +1 slopes are **open**.

## Setting

These are Stein groups `V(Γ,Λ,ℓ)` as in `stein-derived-groups-need-computable-modules`: right-continuous PL
bijections of `[0,ℓ)` with slopes in `Λ` and finitely many breakpoints in `Γ`. On each piece they are
`t ↦ μt + c` with `μ ∈ Λ` and `c ∈ Γ` (Tanner, arXiv:2312.07375, proof of the Zappa--Szép lemma). So they
permute `X := Γ ∩ [0,ℓ)`.

## Theorem

Let `Λ` be finitely generated. Assume:
- (F1) `V(Γ,Λ,ℓ)` is finitely presented;
- (F2) `V(Γ,Λ,ℓ')` is finitely generated for every `ℓ' ∈ Γ ∩ (0,ℓ)`.

Then the action of `V(Γ,Λ,ℓ)` on `X` is of type (A):
- it is faithful;
- the group is finitely presented;
- point stabilizers are finitely generated;
- it is transitive on ordered pairs of distinct points, so there is one orbit of 2-element subsets.

Hence every subgroup of `V(Γ,Λ,ℓ)` has solvable word problem and embeds in the finitely presented simple
twisted Brin--Thompson group `SV_{V(Γ,Λ,ℓ)}` (`type-a-action-gives-boone-higman-for-subgroups`).

## Quadratic instance (corrected)

Let `λ ∈ (0,1)` with `λ² + mλ − 1 = 0`, `m ≥ 1`: the metallic means, which are the quadratic units of norm −1 in
`(0,1)`. Put `Γ = Z[λ]` and `Λ = ⟨λ⟩`. Then (F1) and (F2) hold by `pisot-unit-slope-stein-groups-are-finitely-presented`,
since `1/λ` is a unit with property (F). So every subgroup of `V(Z[λ],⟨λ⟩,ℓ)` satisfies Boone--Higman.

For these slopes this adds little to that node: `D(V)` is itself a finitely presented simple group of finite
index there.

**Norm +1 slopes, such as `λ = 2 − √3`: ESTABLISHED (09-18) by the negative-base nodes.**
- **Update.** `negative-base-pisot-stein-groups-are-finitely-presented` proves (F1) for these slopes, through the
  square of the coding `y ↦ {−βy}`, and (F2) follows since every length is covered. So the theorem here applies,
  with `D(V)` of infinite index (`V^ab ↠ Z`).
- `algebraic-interval-exchange-groups-satisfy-boone-higman` puts `V(Z[λ],⟨λ⟩,ℓ)` inside the flip group `G^±_β`,
  `β = λ^{−1}`, which is a finitely presented contracting RSG on a negative-base coding
  (`negative-base-pisot-stein-groups-are-contracting-rsgs`). So every subgroup embeds in a finitely presented
  simple group, and the type (A) theorem here is not needed for that.
- History: Cleary covers only norm −1 F-versions, and the positive-base RSG route needs (F), which fails for norm
  +1 quadratic units (Akiyama, Proposition 1). `V` is not an RSG in the flip coding itself, since its canonical
  similarities have slopes `(−β)^n`; the square of the coding fixes this.
- The corollary "every real quadratic field" holds again, now with (F1) from the negative-base node. The
  Sturmian case was first covered by bh-free-03's substitutive route
  (`quadratic-rotation-iet-groups-satisfy-boone-higman`).

## Priority

The Sturmian and rotation-IET corollary was landed first by bh-free-03, as
`quadratic-rotation-iet-groups-satisfy-boone-higman` (09-18). That route goes through contracting RSGs. The type (A) theorem for Stein
V-groups and its consequence for arbitrary subgroups of `V(Z[λ],⟨λ⟩,ℓ)` are not covered there. No priority is claimed.

## Not claimed

- Anything for slopes of degree ≥ 3 or transcendental. For transcendental `λ`, `V(Z[λ^{±1}],⟨λ⟩,1)` is not
  even finitely generated, since `H_1` is infinitely generated by Tanner's computation.
- Anything about `SV_V` beyond Zaremsky's Theorem A and Corollary B.
