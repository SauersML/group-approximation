---
rg: 2
id: bernoulli-deficit-window-difference-subgroup-proof
kind: route
title: Dropping disconnected codewords and conjugating by one window element moves a configuration into its difference subgroup
target: bernoulli-deficit-windows-need-a-non-maximal-difference-subgroup
requires:
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
  - bernoulli-rokhlin-maximality-passes-to-subgroups
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
artifacts:
  - research/artifacts/rokhlin-window-localization-and-read-bound-2026-09-12.md
---

Theorem 1.1 and Corollaries 1.2–1.3 of the artifact.

1. Codewords not connected to `F ∩ E^-1` through overlapping reads depend only on sites disjoint
   from the connected reads and from `1`, so they are independent and leave `H(x(1) | y_F)`
   unchanged.
2. Overlapping reads `f e = f' e'` give `f^-1 f' ∈ E E^-1`, so the connected codewords lie in one
   left coset `e_0^-1 H`.
3. Conjugation `s ↦ e_0 s e_0^-1` is a bijection of `G`. It sends each read `f e` to
   `(e_0 f)(e e_0^-1)` with both factors in `H`, and fixes `1`. Pushing the iid field forward along
   it gives the same joint law of the special site and the codewords, so `Phi` is unchanged and
   the configuration lives in `H`.
4. If `H` is infinite and Rokhlin-maximal at `q`, the finitary-witness claim gives `Phi >= log q`.
   If `H` is finite, count over `H`: `|H| k log q <= |H| H(psi) + sum_h H(x(h) | y_(hC''))`, and left
   translation inside `H` preserves reads, so each term is `H(x(1) | y_(C''))`.
5. For `|E| <= 2`, `H` is cyclic. Infinite cyclic groups are sofic, hence Rokhlin-maximal by item 4
   of Seward's import; finite ones fall under step 4. For a window inside a coset of a
   Rokhlin-maximal `K`, `E E^-1` lies in a conjugate of `K`, and subgroups of maximal groups are
   maximal.
