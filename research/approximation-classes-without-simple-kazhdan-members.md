---
rg: 2
id: approximation-classes-without-simple-kazhdan-members
kind: claim
title: Residually finite, locally residually finite, amenable, residually amenable and residually solvable groups contain no infinite simple Kazhdan group
distinct_from:
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: that is the class where simple Kazhdan envelopes exist; this is the list of standard classes where they cannot.
---

**ESTABLISHED (unreviewed).** Let `P` be one of: residually finite, locally residually finite (every finitely generated
subgroup is residually finite), amenable, residually amenable, residually solvable. No infinite finitely generated
simple group with property (T) lies in `P`.

**Consequence for envelope theorems.** For each such `P`, the statement "a finitely generated group is in `P` iff it
is a subgroup of an infinite finitely generated simple Kazhdan group in `P`" fails: `Z ∈ P` has no such host. So the
characterization `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` cannot be pushed down to the residually
finite class. Every residually finite input has a host (`rf-groups-embed-in-simple-kazhdan-lef-groups`), but the host is
LEF and never residually finite.

Route: `approximation-classes-without-simple-kazhdan-members-proof`.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS; every step re-derived (see the artifact).
