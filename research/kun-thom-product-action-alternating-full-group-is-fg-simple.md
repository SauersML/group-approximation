---
rg: 2
id: kun-thom-product-action-alternating-full-group-is-fg-simple
kind: claim
title: The alternating full group of a Kun--Thom wreath acting on lamp configurations times a finite quotient is finitely generated and simple
distinct_from:
  kun-thom-product-action-alternating-full-group-is-nonsofic: that is the nonsofic part, proved with Kun--Thom Theorem A as the only external input; this is simplicity and finite generation, which rest on Nekrashevych's theorems.
artifacts:
  - research/artifacts/kun-thom-alternating-full-group-2026-09-12.md
---

**OPEN.** In the setting of `kun-thom-product-action-alternating-full-group-is-nonsofic`, the alternating full group
`A(Y)` of `W` acting on `Y = {0,1}^(G/Gamma) x G/K` is infinite, finitely generated and simple.

## Attempts

- **Dynamical hypotheses, checked on paper** (artifact Lemma 1.1). The action is minimal and expansive, orbits are
  infinite, and the kernel is `core_G(Gamma) ∩ K <= G`.
- **Imports not re-read.** The recalled statements are Nekrashevych, *Simple groups of dynamical origin* (Ergodic
  Theory Dynam. Systems 39, 2019): minimal implies `A` simple, and expansive with infinite orbits implies `A` finitely
  generated. The source is not on this machine. Close this node by reading the exact hypotheses of both theorems
  (effective groupoid of germs, Hausdorffness, orbit sizes, compact generation) and checking them for `Y`.
- **Not tried.** A direct simplicity proof from the rigid-stabilizer lemma (artifact Lemma 2.1), avoiding the import.
