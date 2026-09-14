---
rg: 2
id: subshift-el3-parabolic-subgroups-are-maximal
kind: claim
title: In EL_3(LC(X,F_2)⋊Z) the stabilizers of the summands e_1R and e_1R⊕e_2R of R^3 are maximal subgroups
artifacts:
  - research/artifacts/sk-free-2-maximal-subgroups-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed)** via `subshift-el3-parabolic-subgroups-are-maximal-proof`.

Let `X` be an infinite minimal subshift, `R = LC(X,F_2) ⋊_T Z` and `G = EL_3(R)`. Then:
- `P = {g ∈ G : g_21 = g_31 = 0}` is a maximal subgroup of `G`;
- `P′ = {g ∈ G : g_31 = g_32 = 0}` is a maximal subgroup of `G`.

As over a field, `G` acts primitively on the `G`-orbit of the "points" `e_1R` and of the "lines" `e_1R ⊕ e_2R` of `R^3`.

Mechanism:
1. A commutator of `g ∉ P` with a small-support root element of `P` lands in a tower copy of `GL_d(F_2)` and outside `P`.
2. Stabilizers of subspaces are maximal in `GL_d(F_2)`.
3. The level ideal `{r : e_21(r) ∈ H}` covers `X`.

**Review (sk-verify-15, 2026-09-13): PASS.** Lemma C1 (all three constructions of C), support alignment, the commutator column formula, the finite maximality step and the level ideals for P and P′ re-derived. See `research/artifacts/sk-verify-15-2026-09-13-part2.md` §1.
