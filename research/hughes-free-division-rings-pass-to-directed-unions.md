---
rg: 2
id: hughes-free-division-rings-pass-to-directed-unions
kind: claim
title: If every member of a directed union of locally indicable groups has a Hughes-free division ring, so does the union
distinct_from:
  fsp-graph-of-rings-and-linnell-extension-imports: that imports existence for amenable, residually torsion-free nilpotent and free-by-cyclic groups; this adds closure under directed unions, which covers infinitely generated locally free groups.
artifacts:
  - research/artifacts/gk3-nonrf-hosts-2026-09-14.md
---

**ESTABLISHED** by [[hughes-free-division-rings-pass-to-directed-unions-proof]].

Let `k` be a division ring and `G = ∪_(i in I) G_i` a directed union of subgroups. Suppose each `G_i` is locally
indicable and `k*G_i` has a Hughes-free division ring `D_i`. Then `G` is locally indicable and `k*G` has a
Hughes-free division ring, the directed colimit of the `D_i`.

**Use.** A locally free group (every finitely generated subgroup free) has a Hughes-free division ring over every
division ring, since free groups do (item 2 of [[fsp-graph-of-rings-and-linnell-extension-imports]]).
