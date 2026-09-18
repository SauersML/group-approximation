---
rg: 2
id: simple-inputs-have-finitely-presented-stabilizer-engines
kind: claim
title: For every infinite finitely generated simple group S with solvable word problem, the derived full group of Z/2 * S on its compactified Bass–Serre tree is finitely presented
requires:
  - free-product-boundary-groupoids-carry-the-vertex-group-homology
distinct_from:
  fp-stabilizer-engines-need-decidable-vertex-groups: that is the proved necessary condition (decidable vertex group); this is the open sufficiency statement for simple inputs.
  stabilizer-engines-force-fp-vertex-groups: that proves a finitely presented engine forces a finitely presented vertex group; this asserted finite presentation of the engine for all decidable simple inputs, which that result refutes.
refuted_by:
  - regular-cyclic-twisted-core-has-non-fp-stabilizer-engine
  - stabilizer-engines-of-non-fp-simple-groups-are-not-fp
---

**REFUTED (2026-09-18)** by `stabilizer-engines-of-non-fp-simple-groups-are-not-fp`: a finitely
presented `D(F_S)` forces `S` to be finitely presented (`fp-stabilizer-engines-need-fp-vertex-groups`,
via a quasi-retraction onto `Z/2 * S`), and `S = D(F_(Z≀Z))` is a decidable finitely generated
simple group that is not. The live form is `fp-decidable-vertex-groups-have-fp-stabilizer-engines`.

**Refuted statement** (stated by bh-free-60, 2026-09-18). Notation `F_B`, `D(F_B)` is as in
`free-product-boundary-groupoids-carry-the-vertex-group-homology`, with `k = 2`.

**Claim.** Let `S` be an infinite finitely generated simple group with solvable word
problem. Then `D(F_S)` is finitely presented.

**Why it matters.** `S` is perfect, so `S ≤ D(F_S)`, and `D(F_S)` is simple. So the
claim gives Boone–Higman through `boone-higman-via-stabilizer-engines`.

**Necessity of the hypothesis.** Solvable word problem cannot be dropped, by
`fp-stabilizer-engines-need-decidable-vertex-groups`.

## What is known

1. **The first test is open.** The first test, `B = Z`, is Reid's group
   (`reid-higman-thompson-variant-d-zero-abelianization`). Its finite presentation is
   open, and a negative answer there would be strong evidence against the claim.
2. **Li's Garside theorem does not apply.** Li's theorem (arXiv:2110.04505, `intro:Gars`)
   needs a locally finite Garside family. In the path category of the tree, every vertex
   is an infinite emitter, and below a vertex no symmetry acts on its branches. So the
   hypothesis fails in the natural presentation.
3. **Doubling the vertices (lane observation, `B = Z`).**
   - Split each vertex point `w` into `w_+` and `w_−`, the limits of its branches `c → +∞`
     and `c → −∞`. Code the first letter `c ≥ 0` as `+1^c0` and `c < 0` as `−1^{|c|−1}0`,
     and later letters by their nonzero differences in the same way.
   - The doubled space is the path space of the 2-state graph `Γ` with states `S` and `U`
     and edges `S→U` (two edges), `U→U` and `U→S`. Its Perron value is 2, and
     `H_0(G_Γ) = Z/2`, `H_1(G_Γ) = 0`.
   - The generators `a_0` and `t` of `Z/2 * Z` act by finitely many prefix replacements.
     For `a_0` these are `+1 ↦ +0+`, `− ↦ +0−`, `+0+ ↦ +1` and `+0− ↦ −`. For `t` they
     are `+ ↦ +1`, `−1 ↦ −` and `−0 ↦ +0`.
   - So Reid's group embeds in Matui's finitely presented full group `[[G_Γ]]`. Its image
     preserves the pairs `{w_+, w_−}` and has linked germs there: the same element of
     `Z/2 * Z` on both sides. The parabolic germ becomes a contracting germ at `w_+`
     linked to an expanding germ at `w_−`.
   - Finite presentation of Reid's group is therefore a question about a linked-germ
     subgroup of an fp SFT full group. It is the analogue of `T ≤ V`, with germ linking
     in place of cyclic order.
4. **Local heuristic.** Near a vertex, `t` and the finitary permutations of branches
   generate a copy of Houghton's `H_2`, which is not finitely presented. A proof of finite
   presentation must show that these relations are consequences of relations supported
   elsewhere.

## Suggested attack

Use a Stein–Farley complex on cone partitions.
- **Cone types.** Types are `j >= 1`, the number of removed branches. The expansion rule
  is `j → (j+1, 1)`, which peels one branch.
- **Descending links.** The descending link of a partition is a complex of capacitated
  matchings between hubs (types `>= 2`, capacity `j − 1`) and leaves (type 1).
- **The difficulty.** The automorphisms of a cone are its local full group. They must be
  replaced by rigid canonical models, for example through the doubled `Γ`-coding of
  item 3.
