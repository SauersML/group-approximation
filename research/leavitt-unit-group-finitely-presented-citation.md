---
rg: 2
id: leavitt-unit-group-finitely-presented-citation
kind: route
title: Import Khanh's finite presentation of the binary Leavitt unit group
target: leavitt-unit-group-finitely-presented
requires: []
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

Citation import, not a reproof. arXiv:2609.08428v1, Theorem 6.1: "The group
G = R^× is finitely presented", with `R = L_{F_2}(1,2)`. Read on 2026-09-11
from the arXiv abstract and from the PDF text of v1, extracted on MSI; labelled
statements are quoted in the artifact.

**Verified on a second pass, whole paper read (2026-09-11).**

- The algebra is the binary Leavitt algebra over `F_2`; the statement concerns
  the full unit group, with no further hypothesis.
- The proof is complete.
  - Krstić–McCool (JPAA 141 (1999), Theorem 3) makes `St_5(R)` finitely
    presented, because `R` is a finitely presented ring (six relators, (6.1)).
  - Theorem 5.4 identifies `St_5(R)` with `GL_5(R)`.
  - The five-leaf coordinates identify `GL_5(R)` with `R^×`.
- A second path avoids Voronetsky's refinement step. Theorem 5.1 already gives
  `St_4(R) ≅ GL_4(R)`, Krstić–McCool covers `n = 4`, and the four-leaf
  coordinates give `GL_4(R) ≅ R^×`.
- Every external input is a published theorem. No gap was found. See the
  artifact's second-pass section.
