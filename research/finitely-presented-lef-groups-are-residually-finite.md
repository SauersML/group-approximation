---
rg: 2
id: finitely-presented-lef-groups-are-residually-finite
kind: claim
title: A finitely presented LEF group is residually finite
distinct_from:
  lef-simple-rings-are-not-finitely-presented: that is the ring analogue for LEF rings; this is the classical group statement.
artifacts:
  - research/artifacts/un-sofic-not-lef-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; standard).** If `Γ` is finitely presented and locally embeddable into finite groups, then `Γ` is
residually finite. Equivalently, a finitely presented group that is not residually finite is not LEF.

A partial embedding of a ball that contains every relator and a word for `g ≠ e` defines a homomorphism to a finite group.
It kills the relators and keeps `g` nontrivial.

Route: `finitely-presented-lef-groups-are-residually-finite-proof`.

**Review (un-verify-3, 2026-09-13): PASS (standard).** A partial embedding of a relator ball defines a finite quotient that separates `g`. `research/artifacts/un-review3-2026-09-13-part3.md` §8.
