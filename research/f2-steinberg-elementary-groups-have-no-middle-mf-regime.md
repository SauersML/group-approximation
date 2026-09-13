---
rg: 2
id: f2-steinberg-elementary-groups-have-no-middle-mf-regime
kind: claim
title: Over F_2, EL_N of a minimal effective Steinberg algebra is MF or MF-rigid for every N >= 3
distinct_from:
  steinberg-elementary-groups-are-simple-mod-centre: that proves EL_n is simple modulo a scalar centre; this reads that for k = F_2 as the collapse of the MF spectrum to one threshold
  stably-finite-simple-rings-have-mf-elementary-groups: that is the open converse of rung (M); this shows that on F_2 Steinberg algebras the converse reduces to its rigidity half
artifacts:
  - research/artifacts/un-m-converse-simple-spectrum-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `𝒢` be a Hausdorff ample groupoid that is minimal and effective, with compact infinite
unit space, and put `R = A_(F_2)(𝒢)`. For every `N ≥ 3`, `EL_N(R)` is either MF or MF-rigid. In the notation of
`mf-rigidity-is-monotone-in-matrix-rank`, the middle regime of `R` is contained in `{2}`.

**Consequence for rung (M⇐).** On this class, `stably-finite-simple-rings-have-mf-elementary-groups` is equivalent to its
*rigidity half*: if `R` is stably finite, then no `EL_N(R)`, `N ≥ 3`, is MF-rigid. The lifting half (an empty middle
regime) is automatic.

**Test object.** The Labbé ring `LC(Ω_U,F_2) ⋊ Z²` is in the class. So if it is not exactly matricial, each `EL_N` over it
(`N ≥ 4`) is non-LEF and either MF or MF-rigid, with no third outcome (artifact §3).

The same conclusion holds for non-Hausdorff ample `𝒢` with a simple Steinberg algebra, through
`ample-steinberg-el-simple-mod-centre-without-hausdorff`. Over `F_q` with `q` odd, a middle rank forces MF to fail to lift
through some nontrivial subgroup of `F_q^× I_N ∩ EL_N(R)`.
