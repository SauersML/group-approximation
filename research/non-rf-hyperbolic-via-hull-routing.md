---
rg: 2
id: non-rf-hyperbolic-via-hull-routing
kind: route
title: Route a known non-residually-finite group through Hull's small-cancellation theorem
target: non-residually-finite-hyperbolic-group
requires: []
artifacts:
  - research/artifacts/hyperbolic-residual-finiteness-audit-2026-08-17.md
---

This program already routes groups through Hull's theorem to move properties
into a quotient with prescribed structure — that is what
`common-quotient-onto-normal-subgroup` and
`defect-normally-generates-torsion-free-quotient` do.  The known non-sofic and
non-residually-finite groups are all available as inputs.  So: route one of
them through Hull and read off a hyperbolic group with the same defect.

Dead: by `hull-quotients-are-not-word-hyperbolic` the output is acylindrically
hyperbolic, which is not the target category.  The gap is not a matter of
sharpening the small-cancellation parameters — the inputs one would want to
route contain `ℤ^2`, and an acylindrically hyperbolic quotient may keep it
while a word-hyperbolic group cannot.

**What survives the demolition.**  Everything this program actually uses Hull
for, which is the acylindrical category throughout.  What dies is the
temptation, encouraged by the abbreviation "(acylindrically) hyperbolic" in
this graph's own prose, to treat a Hull quotient as a source of hyperbolic
examples.
