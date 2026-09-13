---
rg: 2
id: leavitt-tensor-host-unit-groups-l2-acyclic-proof
kind: route
title: Tensor-host frame connectivity plus the frame criterion and leaf coordinates over B ⊗ L
target: leavitt-tensor-host-unit-groups-are-l2-acyclic
requires: [frame-acyclic-rings-have-low-degree-l2-acyclic-gl]
artifacts:
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
  - research/artifacts/boone-higman-leavitt-tensor-hosts-2026-09-12.md
  - research/artifacts/review-boone-higman-leavitt-tensor-hosts-2026-09-12.md
---

Artifact Corollary C.
- `S = B ⊗ L` contains `1 ⊗ L`, so it is infinite.
- Corollary 2.5 of the tensor-host artifact gives `H̃_d(X_r(S)) = 0` for `0 <= d <= r-3`.
  It is Khanh's coning argument over `S`, from simultaneous strong division (its Lemma 2.2 and
  Proposition 2.4). The review verified it (PASS, Section 1). It uses no K-theory hypothesis.
- The frame criterion at `r = n+3` gives `β_n^(2)(GL_(n+3)(S)) = 0`.
- Leaf coordinates with coefficients in `B` give `M_r(S) ≅ S`, so `GL_r(S) ≅ S^x`.
