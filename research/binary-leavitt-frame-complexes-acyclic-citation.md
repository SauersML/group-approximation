---
rg: 2
id: binary-leavitt-frame-complexes-acyclic-citation
kind: route
title: Import Khanh Definition 2.1 and Corollary 4.3
target: binary-leavitt-frame-complexes-are-highly-acyclic
requires: []
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
  - research/artifacts/leavitt-unit-l2-acyclicity-2026-09-12.md
---

H. V. Khanh, arXiv:2609.08428v1, read from `lit-groups/khanh-clean.txt` on MSI, 2026-09-12.
- **Definition 2.1**: "The ordered frame semisimplicial set X_r(A) has as its p-simplices the
  tuples (v_1,...,v_k), where k = p + 1 ≤ r, admitting a decomposition A^r = v_1A ⊕ ··· ⊕ v_kA
  ⊕ C, with C ≅ A^(r−k). Each map A → v_iA, a ↦ v_i a, must be an isomorphism. [...] Faces
  delete vectors, and there are no simplices in dimensions p ≥ r."
- **Proof of Theorem 2.2**: "The group Γ_r acts transitively on the ordered (k−1)-simplices of
  X_r(A). [...] Since the frames are ordered, the stabilizers fix their simplices pointwise."
- **Corollary 4.3**: "For r ≥ 3, one has H̃_d(X_r(R), Z) = 0 for 0 ≤ d ≤ r −3."

The proof cones a finite cycle by prepending one vector that extends every frame in its
support (Proposition 4.2, from Lemma 4.1). The literature lane read the proof chain in full
(`khanh-2609-08428-leavitt-gl-verified-2026-09-11`). Unrefereed v1 preprint.
