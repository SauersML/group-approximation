---
rg: 2
id: countable-rf-groups-embed-in-simple-kazhdan-lef-groups
kind: claim
title: Every countable residually finite group is a subgroup of an infinite finitely generated simple Kazhdan LEF group
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that is the finitely generated case; this is the countable case, which reduces to it through Wilson's 2-generator embedding.
  simple-kazhdan-lef-host-for-countably-many-rf-groups: that is one host for a countable family of finitely generated residually finite groups, landed independently by sk-strong-3; this embeds one countable residually finite group, and that host follows by applying it to the direct sum of the family.
---

Every countable residually finite group `G` is a subgroup of an infinite, finitely generated, simple group with
property (T) that is LEF, so sofic and hyperlinear. Established through the `-proof` route. The route inherits the
review status of `rf-groups-embed-in-simple-kazhdan-lef-groups`, which was unreviewed when this node landed.

**Review (sk-verify-4, 2026-09-13): PASS.** Wilson Theorem A composed with Theorem E. See `research/artifacts/sk-review-4-2026-09-13-part4.md` §3.
