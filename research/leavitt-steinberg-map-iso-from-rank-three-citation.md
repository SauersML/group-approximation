---
rg: 2
id: leavitt-steinberg-map-iso-from-rank-three-citation
kind: route
title: Import Khanh's acyclicity and Steinberg comparison theorems
target: leavitt-steinberg-map-iso-from-rank-three
requires: []
artifacts:
  - research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md
---

Citation import, not a reproof. arXiv:2609.08428v1, Theorem 4.4 ("H_n(GL_r(R),
Z) = 0 for every n > 0 and r ≥ 1") and Theorem 5.4 ("for every r ≥ 3, the
canonical map φ_r : St_r(R) → GL_r(R) is an isomorphism"), `R = L_{F_2}(1,2)`.
Read on 2026-09-11 from the PDF text of v1, extracted on MSI.

**Verified on a second pass, whole paper read (2026-09-11).**

- **Theorem 4.4** follows from the paper's criterion, Theorem 2.2.
  - Proposition 3.2: standard inclusions are zero on homology. It uses
    Ara–Brustenga–Cortiñas' vanishing of `K_*(R)` (Münster J. Math. 2009,
    Theorem 7.6) and an idempotent compression `c`.
  - Corollary 4.3: frame complexes are highly connected, by a common
    transverse vector.
  - The stabilizer spectral sequence with Quillen's finite-field weights, given
    in full.
- **Theorem 5.4** at rank 4 comes from the criterion Theorem 5.1, via Brown's
  presentation theorem, with these inputs:
  - `H_2(GL_3) = 0` and perfectness of `St_3` in the five-term sequence;
  - the centrality Lemma 5.2;
  - simple connectivity of `|X_4(R)|`;
  - `GL_m = E_m` (Lemma 5.3).
- The other ranks `r >= 3` use Voronetsky's refinement isomorphism (JPAA 225
  (2021), §4 Proposition 1), which was not re-read here. So the rank-5 form used
  for the Leavitt–Steinberg fork rests on it as well as on the rank-4 criterion.
- Every external input is published. No gap was found.
