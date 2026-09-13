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
