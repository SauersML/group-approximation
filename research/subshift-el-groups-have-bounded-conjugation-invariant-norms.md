---
rg: 2
id: subshift-el-groups-have-bounded-conjugation-invariant-norms
kind: claim
title: Every conjugation-invariant norm on EL_3(LC(X,F_2)⋊Z) is bounded, and each nontrivial element normally generates the group in boundedly many steps, with non-uniform bounds controlled by invariant measures
artifacts:
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part1.md
  - research/artifacts/sk-free-6-normal-generation-2026-09-13-part3.md
---

**Statement.** Let `X` be an infinite minimal subshift and `G = EL_3(LC(X,F_2) ⋊ Z)`.
1. `G` is bounded in the sense of Burago–Ivanov–Polterovich: every conjugation-invariant norm on `G` is bounded.
2. For every `g ≠ e` there is `N_g` such that every element of `G` is a product of `N_g` conjugates of `g^{±1}`.
3. For a nonempty clopen `V`, `1/inf_μ μ(V) ≤ cw(e_12(χ_V)) ≤ 312(⌊1/inf_μ μ(V)⌋ + 1)`, so `G` is not uniformly simple.

**Status: established** by `subshift-el-groups-bounded-norms-proof` (bounded elementary generation plus bounded normal generation of root elements). UNREVIEWED; queued with sk-verify-13.

## Attempts
Kept for the record; the question was open until part 3.
- **Cut lemma with cyclic corrections (part 1 §4, part 2 §2.2).** Corrections by cyclic shifts inside each component wrap around blocks and leave a degree-1 remainder over an induced system; iterating does not terminate. Part 3 replaces them with end-local Fredholm corrections, whose inverses are banded.
- **Odometer test case (part 2 §2.1).** Block Gauss reduction over `M_k(F_2[t^{±1}])` stops at stable rank 2. Cutting along towers avoids matrix blocks.
- **Via stable rank one (part 2 §2.3).** Not needed; `sr(R_X) = 1` stays open.
