---
rg: 2
id: binary-leavitt-unit-group-l2-acyclic-proof
kind: route
title: Apply the frame criterion at rank n+3 and return to the unit group by a prefix code
target: binary-leavitt-unit-group-is-l2-acyclic
requires: [frame-acyclic-rings-have-low-degree-l2-acyclic-gl, binary-leavitt-frame-complexes-are-highly-acyclic]
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
---

Artifact Corollary B.
- `R` is infinite, since distinct positive words are distinct elements (Khanh (4.1)).
- Khanh Corollary 4.3 at `r = n+3` is the hypothesis of the frame criterion, which gives
  `β_n^(2)(GL_(n+3)(R)) = 0`.
- A complete prefix code `w_1..w_r` gives the ring isomorphism
  `a ↦ (t_(w_i) a s_(w_j))`, inverse `(a_ij) ↦ Σ s_(w_i) a_ij t_(w_j)`. So `GL_r(R) ≅ R^x`,
  and L²-Betti numbers are invariants of the abstract group.
