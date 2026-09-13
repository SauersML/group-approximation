---
rg: 2
id: labbe-relator-shift-periodic-points-carry-trivial-actions
kind: claim
title: For large n every periodic point of every relator shift of Labbé's derived full group carries the trivial action
invalidates:
  - labbe-full-group-lef-via-periodic-relator-shifts
distinct_from:
  labbe-relator-shifts-carry-patch-rich-periodic-points: That is the crux asking for patch-rich periodic points; this is its negation, uniformly in the extension and its radius.
  aperiodic-sft-gated-models-break-refinement-relations: That covers only gated extensions of ChJN's generators; this covers every extension of every finite generating set.
artifacts:
  - research/artifacts/labbe-lef-crux-small-growth-models-2026-09-13.md
---

**ESTABLISHED (unreviewed).** This refutes `labbe-relator-shifts-carry-patch-rich-periodic-points`.

**Setting.** Notation is that of `zd-subshift-full-group-lef-via-periodic-relator-shifts`:
- `Gamma = D([[Z^2 ~ Omega_U]])` with a finite symmetric generating set `S` and cocycle bound `R`;
- extensions `ĉ` of any radius `R' >= R`;
- relator shifts `Z_n`, and hypotheses (H1) and (H2).

**Statement.** There is `n_0 = n_0(S, R)` such that, for all `n >= n_0`, every extension and every periodic
`y ∈ Z_n`, each `ŝ` fixes every point of the shift orbit of `y`. So (H1) and (H2) never hold together.

**Mechanism.**
- The orbit of `y` is a finite `n`-exact `F(S)`-set. Its balls satisfy `|B_k| <= 9 R^2 k^2`, since the ball
  sits on a torus and generators move points by at most `R`.
- `labbe-full-group-finite-small-growth-models-are-trivial` makes the action trivial.
- (H1) and (H2) would force some `ŝ` to move a point that reads a legal patch.

**Consequence.** The spatial LEF route `labbe-full-group-lef-via-periodic-relator-shifts` is dead for every
extension, gated or not. What remains for LEF is the non-spatial crux (C2) of
`labbe-shift-derived-full-group-is-lef`, narrowed by the finite-models theorem.

**Proof:** `labbe-relator-shift-periodic-points-carry-trivial-actions-proof`.
