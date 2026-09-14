---
rg: 2
id: subshift-gl3-iso-forces-strong-orbit-equivalence-odd-q
kind: claim
title: For q odd, if GL_3(LC(X,F_q)⋊Z) ≅ GL_3(LC(Y,F_q)⋊Z) as abstract groups, then the minimal subshifts X and Y are strongly orbit equivalent
distinct_from:
  subshift-gl3-iso-gives-matrix-ring-iso-odd-q: that concludes only a ring (anti-)isomorphism of the 3x3 matrix rings; this carries it to strong orbit equivalence of X and Y themselves, not of height-3 towers
  subshift-elementary-group-isomorphism-forces-orbit-equivalence: that asks the same for the simple groups EL_3/Z and every q, which remains open; this is the GL_3 version for q odd
artifacts:
  - research/artifacts/sk-rigidity-ring-2026-09-13-part1.md
---

Let `q` be odd and `X, Y` infinite minimal subshifts, with `R_X = LC(X,F_q) ⋊ Z`. If `GL_3(R_X) ≅ GL_3(R_Y)` as
abstract groups, then `(X,T)` and `(Y,T)` are strongly orbit equivalent.

Proof (`-proof` route, artifact part 1 §2, Corollary R1): `subshift-gl3-iso-gives-matrix-ring-iso-odd-q` gives
`M_3(R_X) ≅ M_3(R_Y)` or its opposite. Then apply `cantor-crossed-product-matrix-ring-iso-forces-soe` with `m = 3`.

Scope: the simple groups `EL_3(R_X)/Z` and even `q` are not covered (see
`subshift-el3-isomorphisms-are-standard-over-f2` for the note's case `q = 2`).

**Review (sk-verify-3, 2026-09-13): PASS.** Assembly of Zel'manov Corollary 4 (standing assumptions checked, scan not re-read) with the matrix-ring theorem at `m = 3` re-derived. Scope: q odd, GL_3 only, strong orbit equivalence only. See `research/artifacts/sk-review-3-2026-09-13-part4.md` §3.
