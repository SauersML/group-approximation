---
rg: 2
id: rf-toeplitz-subshifts-over-residually-finite-groups
kind: claim
title: Every finitely generated infinite residually finite group has a minimal topologically free Toeplitz subshift that is residually finite in the Kerr–Nowak sense
distinct_from:
  ccg-uniquely-ergodic-toeplitz-subshifts-exist: that imports uniquely ergodic Toeplitz subshifts over residually finite groups; this designs sparse hole fillings that make the subshift Kerr–Nowak residually finite, which the matricial ring theorem needs.
artifacts:
  - research/artifacts/un-rf-beyond-free-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated, infinite, residually finite group. There is a
Toeplitz array `x ∈ {0,1}^Γ` whose orbit closure `X_Γ` is:
1. minimal and a Cantor space, with the orbit of `x` free, so the action is topologically free;
2. residually finite in the sense of Kerr–Nowak;
3. carries an invariant probability measure; the hole density tends to 0, so the array is regular.

**Construction** (artifact §6). Take a chain of finite-index normal subgroups `Γ_m` with trivial intersection and
large successive indices. At each level, the unique hole coset of `Γ_(m-1)` splits into `Γ_m`-cosets: one new
hole, one coset valued `1`, the rest valued `0`.

**Why RF.** The `Γ_M`-periodic configuration equal to `x` on the skeleton and `0` on the hole has every window
equal to a window of `x`: a union bound over the at most `|W|` hole positions finds a translate by `Γ_M` landing
them all in `0`-cosets of level `M+1`. Proposition S (`rf-subshifts-are-periodic-window-approximable`) finishes.

Applications: `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`.

Route: `rf-toeplitz-subshifts-over-residually-finite-groups-proof`.
