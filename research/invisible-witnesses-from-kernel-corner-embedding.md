---
rg: 2
id: invisible-witnesses-from-kernel-corner-embedding
kind: route
title: Push a one-sided pair through the padded kernel-corner embedding
target: leavitt-kaplansky-failures-have-invisible-witnesses
requires:
  - leavitt-unit-group-algebra-embeds-in-kernel-corner
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/scalar-corner-kernel-embedding-2026-09-12.md
---

The prerequisite gives an injective unital multiplicative map `Phi : S -> K^+`.
Multiplicativity sends `b a = 1` to `Phi(b) Phi(a) = 1`. Injectivity keeps
`Phi(a) Phi(b) = Phi(ab) != 1`. `Phi(x) - 1 = (delta(x) - 1) z` lies in `K`, so both
factors evaluate to `1`, and the defect `delta(1 - ab) z` lies in `K`.

For the listed consequences:
- A (V*) witness is a failure of `S`, since `ab = 1` would make `s_0` a unit of `R`.
- `K^+` is a unital subring of `S`, which gives the reverse implication of item 1.
(Artifact Corollary 4.)

*Verified independently by `gk-vf-linear` (2026-09-12): Section 13 of `research/artifacts/gk-vf-linear-verification-2026-09-12.md`.*
