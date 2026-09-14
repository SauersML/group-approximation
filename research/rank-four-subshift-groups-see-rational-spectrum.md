---
rg: 2
id: rank-four-subshift-groups-see-rational-spectrum
kind: claim
title: For N ≥ 4 the rational continuous eigenvalues of a minimal subshift X are an isomorphism invariant of EL_N(LC(X,F_2)⋊Z)
distinct_from:
  subshift-group-model-sizes-see-rational-spectrum: that constrains the sizes of RING-TYPE approximants; this uses rank-four type rigidity to make the constraint hold for ALL finite simple approximants, and so an isomorphism invariant of the abstract group.
  sturmian-elementary-group-lef-growth-is-exp-r-squared: that shows LEF growth does not separate Sturmian slopes; this separates subshifts with different rational spectra (and, consistently, does not separate Sturmian slopes).
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part4.md
  - research/artifacts/sk-verify-14-2026-09-13-part7.md
---

**ESTABLISHED (unreviewed).**
- Let `N >= 4`, `X` an infinite minimal subshift, `G_X^(N) = EL_N(LC(X,F_2) ⋊ Z)`, and `Cyc(X)` the set of orders of
  finite cyclic factors of `X` (the orders of its rational continuous eigenvalues).
- For a f.g. group `G`, `Div(G)` is the set of `m` such that every sequence of finite simple groups converging to `G`
  (any marking) eventually consists of groups `PSL_(M_k)(F_(q_k))` with `m | M_k`. This is an isomorphism invariant.

Then `Div(G_X^(N)) = {m : m | N·c for some c ∈ Cyc(X)}`. So `G_X^(N) ≅ G_Y^(N′)` forces `N·g_∞(X) = N′·g_∞(Y)` as
supernatural numbers. For `N = N′ >= 4`, `X` and `Y` have the same rational continuous eigenvalues.

Examples: for `N >= 4`, EL_N over a Sturmian subshift is not isomorphic to EL_N over the Thue–Morse subshift or over a
Toeplitz subshift with nontrivial periods.

For the note: this is the rank-at-least-four analogue of one strong-orbit-equivalence invariant, bearing on the
rigidity question. Rank three (`G_X` itself) stays open: `subshift-group-finite-simple-shadows-are-ring-models`.

Route: `rank-four-subshift-groups-see-rational-spectrum-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived:
- invariance of `Div` under change of generating set;
- `⊇`: type rigidity and idempotent ranks, with characteristic 2 forced because `2 ∈ ker π`;
- `⊆`: two families of periodic models with distinct prime twists;
- recovery of `Cyc(X)` from the supernatural number `N·g_∞(X)`.

See `research/artifacts/sk-verify-14-2026-09-13-part7.md` §2.
