---
rg: 2
id: rf-free-minimal-zn-actions-have-non-fp-derived-full-groups
kind: claim
title: For a free minimal action of Z^N on the Cantor set that is residually finite in the sense of Kerr–Nowak, the derived subgroup of the topological full group is not finitely presented; this covers all products of minimal Cantor Z-systems and all free Z^N-odometers
distinct_from:
  free-minimal-zn-derived-full-groups-are-never-fp: that is Matui's open question for every free minimal Z^N action; this settles the residually finite ones and leaves exactly the non-residually-finite ones, which include every minimal subsystem of every weakly aperiodic Z^N shift of finite type (zn-subshift-is-rf-iff-periodically-approximable).
  circle-rotation-zd-derived-full-groups-are-not-fp: that handles codings of free circle-rotation Z^d actions by its own argument; this handles every residually finite free minimal Z^N action through LEF.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED (2026-09-18)** through `rf-free-minimal-zn-non-fp-proof`. It combines cited theorems; Ma's theorem was read
at source. Lane bh-free-12, not independently reviewed. No priority is claimed: a bounded check found no statement of
the finite-presentation consequence for `Z^N`, `N >= 2`, in Ma (arXiv:2209.00580) or Matui (arXiv:1602.00383).

## Statement

Let `φ : Z^N ↷ X` be a free minimal action on the Cantor set. Suppose `φ` is **residually finite** (Kerr–Nowak;
Ma's Def. 5.1): for every finite `F ⊆ Z^N` and `ε > 0` there are an `ε`-dense finite set `E ⊆ X` and an action `β` of
`Z^N` on `E` with `d(φ(s)z, β(s)z) < ε` for all `z ∈ E` and `s ∈ F`. Then:

1. `[[φ]]` is LEF, and so is every subgroup (Ma, Theorem 5.5).
2. `D([[φ]])` is not finitely presented.

**Examples of residually finite free minimal `Z^N` actions.**
- **Products.** `φ_1 × ⋯ × φ_N` on `X_1 × ⋯ × X_N`, where each `(X_i, φ_i)` is a minimal homeomorphism of a Cantor
  set and `Z^N` acts coordinatewise. So Matui's question has a negative answer for every product of minimal Cantor
  `Z`-systems: products of Sturmian, Toeplitz or substitution subshifts, odometers, and so on.
- **Free `Z^N`-odometers.** Inverse limits `lim Z^N / L_k` over decreasing finite-index subgroups with trivial
  intersection.

**What remains of Matui's question.** Free minimal `Z^N` actions (`N >= 2`) that are not residually finite. By
`zn-subshift-is-rf-iff-periodically-approximable`, these include every minimal subsystem of every weakly aperiodic
`Z^N`-SFT (for instance the minimal subsystems of Robinson's tiling shift). For those, the LEF obstruction to finite
presentation is not available, which makes them the natural candidates for AIM Problem 2.5 (see the Matui node).
