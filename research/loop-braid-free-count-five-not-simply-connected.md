---
rg: 2
id: loop-braid-free-count-five-not-simply-connected
kind: claim
title: "At free count 5 the forbidden-ring subcomplexes X_n(F) of L_n(LB_*) are not simply connected for n = 7, 8, 9; the coning subcomplex Y at free count 7 is not simply connected"
distinct_from:
  loop-braid-descending-links-are-eventually-simply-connected: that proves X_n simply connected for n at least 8; this shows the forbidden-ring subcomplexes of free count 5 are not simply connected, a sharpness statement at the bottom of the family
artifacts:
  - research/artifacts/zp-loop-braid-forbidden-ring-push-reduction-2026-09-17.md
  - experiments/loop-braid-push-2026-09-17/abelian_colimit.py
  - experiments/loop-braid-push-2026-09-17/abelian_colimit_output.txt
---

Notation is from `loop-braid-forbidden-ring-coning-statement`.

**Claim.**
- (i) For every `n ∈ {7, 8, 9}` (conjecturally every `n ≥ 7`), every `F ⊂ [n]` with `n − |F| = 7`, and distinct free `v, w`, the complex
  `Y_n(F; v, w)` is connected but not simply connected.
- (ii) Consequently, `X_n(F')` is connected but not simply connected whenever `n ∈ {7, 8, 9}` and
  `n − |F'| = 5`. By the `S_n`-symmetry, which normalizes P and permutes types, the choice of the
  sets `F` and `F'` of a given size is irrelevant.

This shows the base value "connected for free count ≥ 5" (artifact Lemma 3.1) is sharp in degree 1.
It also shows that coning off the type-`{v, w}` links does not raise connectivity automatically at
the bottom of the range. The obstruction is 3-torsion, the same prime as Bouc's `H̃_1(M(K_7)) = Z/3`
for matching complexes.
