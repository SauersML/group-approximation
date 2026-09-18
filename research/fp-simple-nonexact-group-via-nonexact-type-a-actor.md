---
rg: 2
id: fp-simple-nonexact-group-via-nonexact-type-a-actor
kind: route
title: A non-exact type (A) actor sits inside a finitely presented simple group, which is then non-exact
target: fp-simple-nonexact-group
requires:
  - some-nonexact-group-has-a-type-a-action
  - type-a-action-gives-boone-higman-for-subgroups
  - exact-groups-are-closed-under-extensions
---

1. By `some-nonexact-group-has-a-type-a-action` (OPEN), a non-exact `G` has a type (A) action.
2. By `type-a-action-gives-boone-higman-for-subgroups` (Zaremsky, arXiv:2405.18354), `G` embeds in a
   finitely presented simple group `K` (a twisted Brin–Thompson group `SV_G`).
3. Exactness passes to subgroups (`exact-groups-are-closed-under-extensions`), so `K` is not exact. ∎

If `amenable-groupoid-full-groups-are-exact` holds, this host lies in no topological full group of an amenable
groupoid. This is the non-amenable route that the synthesis (§6) says a universal construction would need.
