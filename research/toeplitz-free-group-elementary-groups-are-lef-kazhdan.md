---
rg: 2
id: toeplitz-free-group-elementary-groups-are-lef-kazhdan
kind: claim
title: Elementary matrices over a Toeplitz free-group crossed product give finitely generated LEF Kazhdan groups over a simple ring with a non-amenable acting group
distinct_from:
  free-minimal-subshift-elementary-groups-are-simple-kazhdan: that is the Z^d family, which is simple modulo centre and linear sofic; this is a non-amenable acting group with an exact LEF certificate, and simplicity modulo centre is not claimed.
  minimal-subshift-algebra-is-simple-lef-ring: that is the Z coefficient ring behind the Pestov group; this is the first non-amenable acting group giving a simple LEF coefficient ring.
artifacts:
  - research/artifacts/un-measure-residually-finite-lef-rings-2026-09-13-part2.md
---

**ESTABLISHED (unreviewed).** Let `2 <= r < ∞`, `q` a prime power, and `←F_r` the odometer of a nested
chain of finite-index normal subgroups with trivial intersection. Let `X ⊆ Σ^(F_r)` be a uniquely
ergodic Toeplitz subshift, almost 1-1 over `←F_r` (`ccg-uniquely-ergodic-toeplitz-subshifts-exist`),
and put `R = LC(X, F_q) ⋊ F_r`. Then:
1. `F_r ↷ X` is minimal and topologically free, and `R` is a finitely generated simple ring.
2. `R` embeds unitally in `∏_ω M_(N_n)(F_q)`.
3. For every `n >= 3`, `EL_n(R)` is a finitely generated LEF group with property (T), and every
   finitely generated subgroup of `GL_m(R)` is LEF.

**Not claimed.** Simplicity of `EL_n(R)` modulo its centre. That needs root detection with
ball-indexed towers for free minimal actions of non-amenable groups.

Route: `toeplitz-free-group-elementary-groups-are-lef-kazhdan-proof`.

**Review (un-verify-measure, 2026-09-13): PASS.** Odometer freeness, topological freeness and minimality (Gottschalk, recalled) re-derived; all cited inputs now reviewed. See `research/artifacts/un-review-measure-2026-09-13-part1.md` §M8.
