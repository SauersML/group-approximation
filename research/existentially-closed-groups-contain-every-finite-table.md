---
rg: 2
id: existentially-closed-groups-contain-every-finite-table
kind: claim
title: An existentially closed group realizes every finite multiplication table of every group, and a torsion-free one does so for every torsion-free group
distinct_from:
  local-approximation-properties-are-marked-closed: that defines local approximation properties through finite tables and proves they are hereditary and closed; this shows one existentially closed group already contains every finite table that occurs anywhere, so it is locally universal.
  countable-groups-embed-in-countable-existentially-closed-groups: that gives existence of existentially closed overgroups; this is what such a group contains.
---

**ESTABLISHED** through `ec-group-finite-table-realization-proof`.
Elementary; no novelty is claimed.

**Notation.**  As in `local-approximation-properties-are-marked-closed`, for a
finite subset `F` of a group `G` put
`tab_G(F) = (F u F.F, (x,y) |-> xy for x, y in F, 1)`.  Below, `F` always
contains `1`, so the underlying set `S_F = F u F.F` contains `1`.

**Statement.**
1. Let `H` be an existentially closed group, `G` any group and `F <= G`
   finite with `1 in F`.  There is an injective map `psi: S_F -> H` with
   `psi(x y) = psi(x) psi(y)` for all `x, y in F`.  Then `psi(1) = 1`, and
   `psi` is an isomorphism of tables `tab_G(F) -> tab_H(psi(F))`.
2. The same holds when `H` is existentially closed in the class of
   torsion-free groups and `G` is torsion-free.

So every group is locally embeddable into every existentially closed group,
and every torsion-free group into every torsion-free existentially closed
group.
