---
rg: 2
id: nearby-seam-relations-exclude-finite-presentation
kind: route
title: Perturb the intercept without changing finitely many relations, then use the just non-MF quotient obstruction
target: fixed-endpoint-seam-groups-are-hopfian-infinitely-presented
requires:
  - fixed-mf-quotient-kazhdan-extensions-realize-all-word-degrees
  - binary-subshifts-embed-in-three-marked-kazhdan-groups
artifacts:
  - research/artifacts/pestov91-fixed-quotient-arbitrary-complexity-2026-09-13.md
---

Section 5 shows finite prefixes are locally constant away from the
rotation cuts. Thus distinct nearby intercepts give agreement on any
finite relator list. A finite presentation would produce a marked
epimorphism onto a nearby non-MF member. Every proper quotient is MF,
so the map must be a marked isomorphism. Cylinder witnesses, parity
decoding and seam queries would then identify the two intercepts,
a contradiction. A noninjective surjective endomorphism would likewise
identify the non-MF group with an MF proper quotient, proving Hopficity.
