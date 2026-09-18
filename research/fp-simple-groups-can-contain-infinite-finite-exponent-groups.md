---
rg: 2
id: fp-simple-groups-can-contain-infinite-finite-exponent-groups
kind: claim
title: Some finitely presented simple group contains an infinite finitely generated group of finite exponent
distinct_from:
  free-burnside-groups-satisfy-boone-higman: that asks for embeddings of the free Burnside groups themselves; this asks only for some infinite finitely generated subgroup of finite exponent in some finitely presented simple group, which that claim implies.
  almost-automorphism-torsion-subgroups-are-rf: that excludes almost automorphism groups, including V and all Röver–Nekrashevych groups, as hosts; this is the open existence question those exclusions sharpen.
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**OPEN.** There exist a finitely presented simple group `S` and an infinite finitely generated subgroup `E ≤ S` and
an integer `N >= 1` with `e^N = 1` for all `e ∈ E`.

## Why it matters

- **It is necessary for BH.** For odd `N >= 665` the free Burnside group `B(2,N)` is infinite and has solvable word
  problem (Novikov–Adian, cited in `free-burnside-groups-satisfy-boone-higman`). So `boone-higman-conjecture`
  implies this claim, and so does BBMZ Problem 5.3(6) (`free-burnside-groups-satisfy-boone-higman`).
- **A disproof would refute BH.** Proving that no finitely presented simple group contains an infinite finitely
  generated group of finite exponent would refute `boone-higman-conjecture` outright, with the explicit
  counterexample `B(2,665)`.

## Excluded host classes (on main)

A host `S` cannot be, or lie in, any of the following:
- a residually finite group (Zelmanov, `restricted-burnside-finiteness`);
- a group acting properly on a finite product of trees (Serre's fixed point theorem for finitely generated torsion
  groups on trees);
- a hyperbolic group;
- a group acting properly on a finite-dimensional CAT(0) cube complex (Sageev–Wise, recalled in
  `free-burnside-groups-satisfy-boone-higman`);
- the almost automorphism group `𝒩_d` of a rooted regular tree, and so no Higman–Thompson group and no
  Röver–Nekrashevych group `V_d(G)` for any self-similar `G`
  (`almost-automorphism-torsion-subgroups-are-rf`, lane proof).

## Live candidate hosts

1. **Brin–Thompson groups `nV`, `n >= 2`.** They are finitely presented and simple (Brin). The almost-automorphism
   argument fails there, because the depth cocycle is a vector. The torsion problem in `2V` is undecidable (Belk–
   Bleak arXiv:1405.0982, cited). A withdrawn preprint (arXiv:2209.11982, withdrawn; abstract read) had claimed
   "similar obstructions as Thompson's group V on the torsion subgroups" for `nV`. So whether `2V` is torsion locally
   finite appears open. A f.g. infinite torsion subgroup of `2V` of finite exponent would prove this claim.
2. **Twisted Brin–Thompson groups `SV_Γ`.** These are finitely presented and simple whenever `Γ` has an action of
   type (A) (Zaremsky arXiv:2405.18354, Thm A). So this claim follows from: some infinite f.g. group of finite
   exponent embeds in a group with a type (A) action. That is the permutational Boone–Higman question for such a
   group (`permutational-boone-higman-conjecture`).
3. **Other finitely presented simple groups:** simple Kac–Moody lattices acting on buildings, and simple groups from
   other constructions. Proper actions on buildings do not obviously force torsion subgroups to be finite, and
   whether CAT(0) groups can contain infinite torsion subgroups is a known open question. None of these is excluded
   here.

## Attempts

1. **bh-free-12, 2026-09-18.** Stated the claim and its role as a necessary condition, and landed the exclusion of
   almost automorphism groups. No candidate host was decided.
