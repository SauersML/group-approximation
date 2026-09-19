---
rg: 2
id: cat0-factors-kill-bader-shalom-universality-proof
kind: route
title: "Proof: the golden-mean probe fixes a point in every finite-dimensional CAT(0) space (Izeki-Karlsson), so it lands in a compact stabilizer; the Bader-Shalom projection is injective, and a finitely generated infinite simple group has no nontrivial map to a compact group"
target: cat0-factors-kill-bader-shalom-universality
requires:
  - bader-shalom-normal-subgroup-theorem
  - izeki-karlsson-torsion-groups-fix-cat0-points
  - fg-infinite-simple-groups-are-minimally-almost-periodic
  - nekrashevych-golden-mean-fragmentation-group-properties
  - golden-mean-periodic-group-lies-in-a-contracting-rsg
  - subgroups-of-fp-simple-groups-have-solvable-wp
  - fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree
  - one-haagerup-factor-kills-bader-shalom-universality
---

**Setting.** `Γ < G_1 × G_2` is as in `bader-shalom-normal-subgroup-theorem`
with `n = 2`. Each `G_i` is a locally compact group, hence Hausdorff. The
closure of a subgroup of a Hausdorff topological group is a subgroup, so the
closure of a relatively compact subgroup is a compact subgroup.

**Item 1.** Let `Λ ≤ Γ` be finitely generated, torsion and of subexponential
growth. Let `G_j` act by isometries on a complete CAT(0) space `Y` of finite
dimension. Then `Λ` acts on `Y` through `p_j`. By
`izeki-karlsson-torsion-groups-fix-cat0-points`, item 1, there is `y ∈ Y` with
`p_j(Λ) ⊆ Stab_{G_j}(y)`. If `G_j` is a CAT(0)-compact factor, take `Y` to be the
space in that definition. Then `Stab_{G_j}(y)` is relatively compact, so
`K := cl Stab_{G_j}(y)` is a compact subgroup of `G_j` containing `p_j(Λ)`. By
`bader-shalom-normal-subgroup-theorem`, item 2, `p_j` is injective on `Γ`, hence
on `Λ`. So `p_j|_Λ : Λ → K` is an embedding into a compact group.

**Item 2.** Let `G_j` be a CAT(0)-compact factor, and suppose `Λ ≤ Γ` is
infinite, finitely generated and simple.
- If `Λ` is periodic of subexponential growth, item 1 gives an injective
  homomorphism `Λ → K` into a compact group.
- If `Λ` is weakly Liouville, then the same argument with item 2 of
  `izeki-karlsson-torsion-groups-fix-cat0-points` in place of item 1 gives an
  injective homomorphism `Λ → K` into a compact group.

Since `Λ ≠ 1`, that homomorphism is nontrivial. This contradicts
`fg-infinite-simple-groups-are-minimally-almost-periodic`.

**Item 3.** By `nekrashevych-golden-mean-fragmentation-group-properties`, item 1,
`F` is finitely generated, periodic and of intermediate growth. Also
`P = [F,F]` is simple and of finite index in `F`.
- *Finitely generated.* `P` is a finite-index subgroup of a finitely generated
  group (Schreier).
- *Periodic.* It is a subgroup of a periodic group.
- *Infinite.* `F` has intermediate growth, so `F` is infinite, and a
  finite-index subgroup of an infinite group is infinite.
- *Subexponential growth.* Write each generator of `P` as a word of length at
  most `C` in the generators of `F`. Then the ball of radius `n` in `P` lies in
  the ball of radius `Cn` in `F`, so `β_P(n) ≤ β_F(Cn)`, which is subexponential.
- *Solvable word problem.* By `golden-mean-periodic-group-lies-in-a-contracting-rsg`,
  item 3, `P` is a finitely generated subgroup of a finitely presented simple
  group `Q`. By `subgroups-of-fp-simple-groups-have-solvable-wp`, `P` has
  solvable word problem.

So `P` satisfies the hypothesis of P1.

**Item 4.** By `fg-groups-have-simple-kazhdan-hosts-of-same-wp-degree`, items 1-3,
applied to the input `P`, there is an infinite, finitely generated, simple
Kazhdan group `H_P ⊇ P` with `WP(H_P) ≤_T WP(P)`. By item 3, `H_P` has solvable
word problem. Suppose P1 embeds `H_P` in some `Γ < G_1 × G_2`. Fix `i`.
- *Not Haagerup.* `Γ` contains the infinite finitely generated simple Kazhdan
  group `H_P`. So item 2 of `one-haagerup-factor-kills-bader-shalom-universality`
  shows that `G_i` is not Haagerup.
- *Not CAT(0)-compact.* `Γ` contains `P`, so item 2 above applied to `Λ = P`
  shows that `G_i` is not a CAT(0)-compact factor.
- *Non-compact closures.* `p_i` is injective. So if `cl p_i(P)` or `cl p_i(H_P)`
  were compact, `p_i` would give a nontrivial homomorphism from an infinite
  finitely generated simple group to a compact group. That contradicts
  `fg-infinite-simple-groups-are-minimally-almost-periodic`.
- *Fixed points.* By item 1 applied to `Λ = P`, `p_i(P)` fixes a point in every
  isometric action of `G_i` on a finite-dimensional complete CAT(0) space.

If P1 is applied only to `S = P`, the proofs of the second, third and fourth
points use only `P ≤ Γ`, so they still hold. ∎

**On the classes killed.** Suppose a locally compact `G` acts continuously and
properly on a metric space `Y`. Then for each `y ∈ Y` and each compact
neighbourhood `B` of `y`, the set `{g : gB ∩ B ≠ ∅}` is compact. It contains
`Stab(y)`, which is closed by continuity. So `Stab(y)` is compact. Closed
subgroups of the automorphism groups of locally finite buildings and cube
complexes act this way on their CAT(0) realizations. The two standard facts
behind that sentence are recorded under Trust in the claim.
