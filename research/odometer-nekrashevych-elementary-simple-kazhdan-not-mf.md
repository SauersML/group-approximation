---
rg: 2
id: odometer-nekrashevych-elementary-simple-kazhdan-not-mf
kind: claim
title: EL_N over the F_q-Steinberg algebra of the odometer's Nekrashevych groupoid mod centre is an infinite fg simple Kazhdan group with no nontrivial MF quotient
distinct_from:
  paradoxical-steinberg-families-kazhdan-no-mf-quotient: that gives finite generation, (T) and no MF quotient for every self-similar action, without simplicity; this adds simplicity modulo centre for the odometer, and every pseudo-free one-vertex self-similar action, through Exel–Pardo Hausdorffness.
  grigorchuk-steinberg-algebra-not-simple-over-f2: that is the firewall at the non-Hausdorff Grigorchuk groupoid; this is a pseudo-free, Hausdorff case where the simplicity theorem applies.
artifacts:
  - research/artifacts/un-boundary-families-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed; proof in `odometer-nekrashevych-elementary-simple-kazhdan-not-mf-proof`).**

**Setting.** `G = Z = <a>` acts self-similarly on `X = {0, 1}`: `a·0 = 1` with `φ(a, 0) = 1`, and `a·1 = 0` with
`φ(a, 1) = a` (the binary odometer). `𝒢` is its Nekrashevych groupoid, the Exel–Pardo groupoid of the one-vertex
graph with two loops. `q` is a prime power and `N >= 3`.

**Statement.** `EL_N(A_(F_q)(𝒢))/Z` is an infinite finitely generated simple group with property (T). Every
homomorphism from it to an MF group is trivial.

The same proof covers every pseudo-free one-vertex self-similar action of a finitely generated group with `|X| >= 2`.

**Review (un-verify-3, 2026-09-13): PASS.** Checked pseudo freeness: `φ(a^(2k), x) = a^k`, so `a^n x = x` with trivial restriction forces `n = 0`. Hausdorff via Exel–Pardo Prop `EssFreePath` and Thm `MainHausdorff`; minimal via Thm `CharacMinimal` (one vertex means weakly transitive); effective as a groupoid of germs; full defect `t_1(1 − s_0t_0)s_1 = 1` from the Leavitt generators; finite generation from `paradoxical-steinberg-families-kazhdan-no-mf-quotient` (un-verify PASS). The Exel–Pardo statements match arXiv:1409.1107 plain-TeX source verbatim (l.1342, 1351, 3347, 3557; standing hypothesis l.700). `research/artifacts/un-review3-2026-09-13-part4.md` §7.
