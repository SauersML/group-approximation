---
rg: 2
id: un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical
kind: claim
title: Every rung of the UN ladder kills homomorphisms to residually finite groups for free, so the paradox/measure dichotomy lives entirely in the gap between RF and MF targets
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
---

**ESTABLISHED (2026-09-13, unreviewed)** through
`un-ladder-rf-rigidity-is-free-mf-rigidity-proof`.

Let `R` be a unital ring, `n >= 3`, `G = EL_n(R)`, `Z = Z(G)`, and suppose `S = G/Z`
is infinite and simple. Then:

1. `G` is perfect.
2. `G` has no nontrivial finite quotient.
3. Every homomorphism from `S` to a residually finite group is trivial.

**Why this matters for the ladder.** Hypothesis "`S` infinite simple" holds at *every*
rung, paradox and measure alike, by
`steinberg-elementary-groups-are-simple-mod-centre`. So rigidity against residually
finite targets is free: it follows from simplicity and perfectness and sees nothing of
the dynamics. What the paradox side actually buys is rigidity against the strictly
larger class of MF targets (tex Cor l.1016), while the measure side is itself LEF, hence
MF, and admits a faithful MF model.

With `RF ⊆ LEF ⊆ MF` as classes of groups, the whole UN dichotomy is located in the gap
`RF ⊊ MF`. This explains why the non-MF paper states its theorems for MF targets: over
any smaller target class the same conclusions hold for trivial reasons and carry no
dynamical information.

**Uniform corollaries, same both sides.** With property (T)
(`elementary-groups-over-fg-rings-have-property-t`), `S` also has property FH
(Delorme–Guichardet) and property FA (Watatani), so no nontrivial action on a tree and
no fixed-point-free affine isometric action on a Hilbert space. By Malcev's theorem that
finitely generated linear groups over a field are residually finite, item 3 gives:
every finite-dimensional linear representation of `S` over every field is trivial, and
`S` is not linear. Malcev and the FH/FA implications are cited from standard knowledge
and were not re-read from sources in this lane.
