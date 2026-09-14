---
rg: 2
id: discrete-kazhdan-groups-are-finitely-generated
kind: claim
title: Every discrete Kazhdan group is finitely generated
artifacts:
  - GroupApproximation/Kazhdan/KazhdanFiniteGeneration.lean
---

Every discrete group with property `(T)` admits a finite symmetric generating
set.

This is kernel-checked as
`KazhdanFiniteGeneration.exists_symmetric_generating_finset`; in particular,
the finite-generation hypothesis in residual-finiteness obstructions applies
automatically to every Kazhdan kernel.

**Literature locator (sk-verify-23, 2026-09-14, read at source).** Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, authors' draft of February 23, 2007, §1.3, p.41, Theorem 1.3.1: "Let G be a locally compact group with Property (T). Then G is compactly generated. In particular, a discrete group Γ with Property (T) is finitely generated." It is attributed there to Kazhdan, and the proof on p.41–42 is the quasi-regular argument of the route. The printed 2008 edition was not opened.
