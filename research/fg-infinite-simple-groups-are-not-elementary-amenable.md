---
rg: 2
id: fg-infinite-simple-groups-are-not-elementary-amenable
kind: claim
title: A finitely generated infinite simple group is not elementary amenable
distinct_from:
  elementary-amenable-groups-are-quasidiagonal: that is an approximation property every elementary amenable group has; this says no finitely generated infinite simple group belongs to the class at all
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part1.md
---

**ESTABLISHED.** Let `G` be finitely generated, infinite and simple. Then `G` is
not elementary amenable. Here the class `EG` of elementary amenable groups is the
smallest class containing all finite and all abelian groups and closed under
subgroups, quotients, extensions and directed unions.

The statement is due to Chou, "Elementary amenable groups", Illinois J. Math. 24
(1980), 396–407. Chou's paper was not re-read. The proof in the artifact, Section 2,
is self-contained.

**Consequences.**
- An answer to Zaremsky Problem 1.10 is a finitely presented amenable group that
  is not elementary amenable, so it also answers the finitely presented form of
  Problem 1.12.
- "Finitely generated" cannot be dropped. The finitary alternating group on a
  countable set is infinite, simple and locally finite, hence elementary amenable.

**Proof:** `fg-infinite-simple-groups-are-not-elementary-amenable-proof`.
