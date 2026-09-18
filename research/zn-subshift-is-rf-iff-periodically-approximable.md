---
rg: 2
id: zn-subshift-is-rf-iff-periodically-approximable
kind: claim
title: A Z^N-subshift is a residually finite action (Kerr–Nowak) if and only if its patterns are uniformly approximable by configurations with finite orbit, so minimal subsystems of weakly aperiodic shifts of finite type are never residually finite
distinct_from:
  rf-free-minimal-zn-actions-have-non-fp-derived-full-groups: that uses residual finiteness to get LEF and non-finite-presentation; this characterizes residual finiteness for subshifts and shows where it fails.
  free-minimal-zn-derived-full-groups-are-never-fp: that is Matui's question; this identifies the actions for which the LEF route to it is unavailable.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED (2026-09-18)** through `zn-subshift-rf-periodic-approximation-proof`. Lane proof (bh-free-12),
elementary, not independently reviewed. No priority is claimed.

## Statement

Let `X ⊆ A^(Z^N)` be a subshift, with `A` finite and `X` perfect, and with the standard metric
`d(x,y) = 2^(−min{|v|_∞ : x_v ≠ y_v})`. For `r >= 1`, an **`r`-model family** of `X` is a finite set of configurations
`y^1, …, y^m ∈ A^(Z^N)` such that

- (M1) each `y^j` has finite `Z^N`-orbit, i.e. it is invariant under a finite-index subgroup;
- (M2) every `r`-window `y^j|_(v + B_r)` is a pattern of `X`;
- (M3′) every `r`-pattern of `X` occurs in some `y^j`.

1. The shift action on `X` is residually finite (Kerr–Nowak, as in Ma's Def. 5.1) **if and only if** `X` has an
   `r`-model family for every `r`. For minimal `X`, a single configuration suffices at each radius.
2. **Corollary.** Let `Y ⊆ A^(Z^N)` be a *weakly aperiodic* SFT, i.e. one with no configuration of finite orbit, and let
   `∅ ≠ X ⊆ Y` be any subshift. Then the shift action on `X` is not residually finite. In particular every minimal
   subsystem of a weakly aperiodic `Z^N`-SFT (`N >= 2`) is a minimal Cantor system to which Ma's LEF theorem does not
   apply. It is free when `Y` is strongly aperiodic.
3. **Inverse limits.** If every subshift factor of a Cantor `Z^N`-system is residually finite, so is the system. Only
   this direction is proved.

## Consequence for Matui's question

For free minimal `Z^N` actions, `rf-free-minimal-zn-actions-have-non-fp-derived-full-groups` settles the residually
finite case. By item 2 the remaining case contains every minimal subsystem of every weakly aperiodic `Z^N`-SFT. That is
exactly where finite presentation of `D([[φ]])` is not blocked by LEF. It matches the heuristic that a *finitely
presented* full group needs "finite type" data, as for Matui's one-sided shifts of finite type.
