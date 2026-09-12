---
rg: 2
id: stw99-problem-xliii-untwisted-groupoid-models
kind: claim
title: Every classifiable C*-algebra is an untwisted etale groupoid algebra (STW Problem XLIII)
root: true
artifacts:
  - research/artifacts/stw99-presentations-cartan-cluster-2026-08-30.md
---

**Problem XLIII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**
Given a classifiable C\*-algebra `A`, is there an étale groupoid `𝒢`
with `A ≅ C*(𝒢)`?

Known: with a TWIST, yes — Xin Li (Invent. Math.), building Cartan
subalgebras through Elliott's range-of-invariant inductive limits and
Renault reconstruction; the twist is removable when `K_0` is
torsion-free (Li, Cor 1.8(i)).  Deeley--Putnam--Strung's orbit-breaking
gives genuinely dynamical untwisted models allowing much `K_0`-torsion
but with restricted trace spaces (DPS, Math. Ann. Thm 6.3).

## Attempts

* The open cell is exactly: `K_0`-torsion together with trace spaces
  outside the DPS range.  The two known methods are complementary
  along precisely those two axes (Li: all traces, no torsion without
  twist; DPS: torsion, few traces), so the natural attack is an
  orbit-breaking construction performed fibrewise over Li's Cartan
  systems — break orbits inside each inductive stage to kill the twist
  while Li's machinery carries the trace simplex.  The obstruction to
  merging: orbit-breaking changes `K`-theory by design (that is how it
  inserts torsion), so it must be run against a PRE-corrected
  invariant; no range-of-invariant statement for the broken groupoids
  at Poulsen-type trace simplices exists.  Recorded as the missing
  lemma; nothing suggests an actual obstruction to untwisted models.
