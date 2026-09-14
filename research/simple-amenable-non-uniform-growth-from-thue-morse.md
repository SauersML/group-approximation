---
rg: 2
id: simple-amenable-non-uniform-growth-from-thue-morse
kind: route
title: Take the derived topological full group of the Thue–Morse subshift
target: simple-amenable-group-of-non-uniform-exponential-growth
requires:
  - dyadic-substitution-derived-full-groups-non-uniform-growth
  - derived-full-group-of-cantor-minimal-system-is-simple
  - derived-full-group-fg-iff-minimal-subshift
  - minimal-cantor-full-groups-are-amenable
---

- The Thue–Morse substitution `0↦01, 1↦10` is primitive, of constant length 2, and its fixed point is not periodic.
- So its two-sided subshift `(X,T)` is an infinite minimal subshift, and `[[T]]′` has non-uniform exponential growth by `dyadic-substitution-derived-full-groups-non-uniform-growth`.
- `[[T]]′` is simple (`derived-full-group-of-cantor-minimal-system-is-simple`) and finitely generated (`derived-full-group-fg-iff-minimal-subshift`).
- It is infinite (it contains a lamplighter group) and amenable as a subgroup of `[[T]]` (`minimal-cantor-full-groups-are-amenable`).
