---
rg: 2
id: every-braid-group-cat0-from-infinitely-many-strands
kind: route
title: Braid groups are all CAT(0) once infinitely many are, because CAT(0) passes to fewer strands
target: every-braid-group-is-cat0
requires:
  - braid-groups-cat0-for-infinitely-many-strands
  - braid-cat0-passes-to-fewer-strands
artifacts:
  - research/artifacts/braid-cat0-fewer-strands-2026-09-16.md
---

## Why sufficient

Let `S = {n ≥ 1 : B_n acts geometrically on a complete CAT(0) space}`.

- `braid-cat0-passes-to-fewer-strands` says `n + 1 ∈ S ⇒ n ∈ S` for every
  `n ≥ 1`.
- By induction on `m − n`, `m ∈ S` and `n ≤ m` imply `n ∈ S`.
- `braid-groups-cat0-for-infinitely-many-strands` says `S` is infinite. So for
  every `n ≥ 1` there is `m ∈ S` with `m ≥ n`, and hence `n ∈ S`.

So `S = Z_{≥1}`, which is `every-braid-group-is-cat0`. This is Corollary 5.2 of
the artifact. ∎
