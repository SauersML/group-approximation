---
rg: 2
id: virtually-infranormal-kazhdan-mf-detection
kind: claim
title: Kazhdan shadow detection needs only finitely many cosets of the compressor-generated subgroup
distinct_from:
  hyperlinear-killed-normal-kazhdan-mf-transfer: that assumes a normal Kazhdan subgroup; this allows infranormality inside a finite-index subgroup.
  kazhdan-projection-finite-target-calculus: that centralizes a projection under each compressor; this turns that fact into operator-norm invisibility from the universal HS hypothesis.
artifacts:
  - research/artifacts/infranormal-mf-detection-2026-09-13.md
---

Let `G` be countable, `K <= G` have property (T), and
`H = <{g in G : g K g^-1 <= K}>`. If `[G:H]` is finite, then

`K <= S(G)` if and only if `K <= Rad_MF(G)`.

Here `S(G)` is universal normalized-HS invisibility for operator-norm
asymptotic unitary representations. In particular the one-sided
compression criterion remains valid with its normality hypothesis on `K`
replaced by this finite-index condition. Mathematical proof only;
this claim does not assert a new Lean formalization or a new example.
