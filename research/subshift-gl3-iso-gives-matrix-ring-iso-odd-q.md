---
rg: 2
id: subshift-gl3-iso-gives-matrix-ring-iso-odd-q
kind: claim
title: For q odd, an abstract isomorphism GL_3(LC(X,F_q)⋊Z) ≅ GL_3(LC(Y,F_q)⋊Z) forces M_3(R_X) ≅ M_3(R_Y) or its opposite as rings
distinct_from:
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that is about the simple projective groups S_X = EL_3/Z and asks for strong orbit equivalence; this is the GL_3 version of step (a) only, and it concludes a ring (anti-)isomorphism of 3x3 matrix rings
artifacts:
  - research/artifacts/un-orbit-equivalence-2026-09-13-part1.md
---

Let `q` be odd, and let `X, Y` be infinite minimal subshifts with `R_X = LC(X,F_q) ⋊_T Z`. If `GL_3(R_X) ≅ GL_3(R_Y)`
as abstract groups, then `M_3(R_X) ≅ M_3(R_Y)` or `M_3(R_X) ≅ M_3(R_Y)^op` as rings.

It follows from Zel'manov's Corollary 4 (`zelmanov-standard-isomorphisms-linear-groups-with-half`), because both
matrix rings are simple. Full proof in the `-proof` route and in artifact part 1 §2.

Scope:
- `q` even is not covered, since Zel'manov assumes `1/2`.
- The projective groups `S_X = EL_3(R_X)/Z` are not covered; see artifact §3, firewalls F-PE1 and F-PE2.
- The conclusion is about `M_3`, so downstream `K_0` arguments see the order unit `3[1]`.

**Review (sk-verify-3, 2026-09-13): PASS, conditional on the Zel'manov import as quoted.** `1/2` in both rings, `φ(G) = S* ⊇ φ(Σ)_S`, generation of `M_3(R_Y)` by `GL_3(R_Y)` (Lemma G1) and simplicity of `M_3(R)` re-derived. See `research/artifacts/sk-review-3-2026-09-13-part4.md` §3.
