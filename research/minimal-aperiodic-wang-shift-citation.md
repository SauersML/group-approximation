---
rg: 2
id: minimal-aperiodic-wang-shift-citation
kind: route
title: Import Labbé's theorem that the 19-tile Wang shift is self-similar, aperiodic and minimal
target: minimal-aperiodic-wang-shift-exists
requires: []
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**Citation import.** Read on 2026-09-12 from the arXiv TeX source on MSI (`/scratch.global/sauer354/fpsz2/src/1802.03265.d/article1.tex`).

J. Labbé, *A self-similar aperiodic set of 19 Wang tiles*, arXiv:1802.03265:
- **Definitions** (lines 225–240): tiles sit on integer lattice points without rotation. A tiling is valid if every pair of contiguous edges has the same colour. `Omega_T` is the set of all valid tilings `Z^2 -> T`, and a nonempty Wang shift is aperiodic if none of its tilings has a nontrivial period.
- **Theorem 1** (line 296): "The Wang shift `Omega_U` is self-similar, aperiodic and minimal."

**What the claim adds.**
- The Wang shift condition is local, since it checks the right and upper neighbours, so `Omega_U` is a subshift of finite type.
- Aperiodic and nonempty means every stabilizer is trivial, so the action is free.
- A free action forces `Omega_U` to be infinite. Being minimal and infinite, it has no isolated points, so it is a Cantor set.

**Not reproved here:** the recognizability and self-similarity argument behind Labbé's theorem.
