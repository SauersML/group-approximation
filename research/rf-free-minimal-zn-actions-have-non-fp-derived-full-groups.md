---
rg: 2
id: rf-free-minimal-zn-actions-have-non-fp-derived-full-groups
kind: claim
title: For a free minimal action of Z^N on the Cantor set that is residually finite in the sense of Kerr–Nowak, the derived subgroup of the topological full group is not finitely presented; this covers all products of minimal Cantor Z-systems and all free Z^N-odometers
distinct_from:
  free-minimal-zn-derived-full-groups-are-never-fp: that is Matui's open question for every free minimal Z^N action; this settles the residually finite ones and leaves exactly the non-residually-finite ones, which include every minimal subsystem of every weakly aperiodic Z^N shift of finite type (zn-subshift-is-rf-iff-periodically-approximable).
  circle-rotation-zd-derived-full-groups-are-not-fp: that handles codings of free circle-rotation Z^d actions by its own argument; this handles every residually finite free minimal Z^N action through LEF.
  zd-derived-full-group-fp-forces-finite-type: that shows a free minimal Z^d-subshift with finitely presented derived full group is of finite type; since a residually finite free minimal subshift is never of finite type, that theorem already gives this node's non-finite-presentation conclusion for subshifts, and this node adds only LEF of the full group and the non-subshift Cantor case.
  periodic-approximable-subshifts-host-no-fp-simple-group: that kills finitely presented infinite simple subgroups of full groups of periodically approximable subshifts through SFT neighbourhoods; for free subshifts periodic approximability is the Kerr–Nowak residual finiteness used here (zn-subshift-is-rf-iff-periodically-approximable), so for subshifts the two nodes overlap.
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

## Relation to main (correction, 2026-09-18, bh-free-12)

For **subshifts** the headline of this node was already on main when it landed. Two nodes give it:
- `zd-derived-full-group-fp-forces-finite-type`, which shows that finite presentation of `D` forces finite type;
- `periodic-approximable-subshifts-host-no-fp-simple-group`.

Indeed a residually finite free minimal subshift `X` is never of finite type.
- Suppose `X` is an SFT with forbidden patterns of radius `r_0`.
- A model family at radius `r >= r_0` (`zn-subshift-is-rf-iff-periodically-approximable`) gives a configuration of
  finite orbit all of whose `r`-windows are `X`-legal. That configuration then lies in `X`.
- This contradicts freeness.

What this node adds beyond main:
- `[[φ]]` itself is LEF, by Ma's Theorem 5.5.
- The argument does not need `X` to be a subshift: it covers, e.g., free `Z^N`-odometers.
  - For non-expansive actions `D([[φ]])` is not even finitely generated
    (`free-action-fg-alternating-full-groups-force-expansivity`), so there the non-finite-presentation conclusion needs no
    LEF argument. What this node adds for them is that `[[φ]]` itself is LEF.

## Lesson for general BH

Full groups of Z^N-dynamics can host finitely presented simple groups only on **strongly aperiodic SFTs**:
- finite type is forced (`zd-derived-full-group-fp-forces-finite-type`);
- periodic approximation is forbidden (this node and `periodic-approximable-subshifts-host-no-fp-simple-group`).

Those are exactly the tilings that simulate Turing machines. So any Boone–Higman host built from Z^N-dynamics has to
put its complexity into aperiodic-tiling computation. A finitely presented simple host that simulates only periodic,
residually finite or odometer data cannot exist in this class.
