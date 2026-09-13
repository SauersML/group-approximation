---
rg: 2
id: type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group-proof
kind: route
title: "Characterize FH_3 by superperfect kernels, via the acyclic-kernel criterion and Hopf's theorem"
target: type-fh3-iff-fp3-and-superperfect-kernel-over-fp-group
requires:
  - fn-groups-mod-acyclic-normal-subgroups-are-type-fhn
  - proper-and-free-type-fhn-coincide
  - type-fhn-groups-are-of-type-fpn
artifacts:
  - research/artifacts/zp-fpn-fhn-2026-09-13-part2.md
---

(⇐) A finitely presented `Q` is of type `F_2`, and a superperfect `P` has
`H̃_i(P) = 0` for `i ≤ 2`. Apply
`fn-groups-mod-acyclic-normal-subgroups-are-type-fhn` with `n = 3`.

(⇒)
1. By `proper-and-free-type-fhn-coincide`, take a free 2-acyclic `G`-CW
   complex `Y` with finitely many orbits of cells, truncated to dimension 3.
2. `Y → Y/G` is a regular covering of a finite complex. So
   `Q = π_1(Y/G)` is finitely presented and `P = π_1(Y)` is its kernel onto
   `G`.
3. `H_1(P) = H_1(Y) = 0`.
4. Build `K(P,1)` from `Y` by attaching cells of dimension `≥ 3`. Attaching
   3-cells only quotients `H_2` and higher cells leave it unchanged, so
   `H_2(Y) = 0` surjects onto `H_2(P)`.
5. `FP_3` holds by `type-fhn-groups-are-of-type-fpn`.

Theorem D of `research/artifacts/zp-fpn-fhn-2026-09-13-part2.md`, §6.
Unreviewed.
