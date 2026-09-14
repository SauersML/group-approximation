---
rg: 2
id: subshift-group-model-sizes-see-rational-spectrum-proof
kind: route
title: Grade the word graphs, rank-count conjugate idempotents, and count covering walks against proper powers
target: subshift-group-model-sizes-see-rational-spectrum
requires: [subshift-algebra-groups-embed-in-marked-groups, four-regular-simple-expander-limits-encode-word-graphs]
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part2.md
---

Full proof in the artifact.
- **Grading (§1).** A strongly connected graph of period `g` has a `Z/g`-grading increasing along edges. On the word
  graph this is a cyclic factor depending on `x_[0,r)`. Conversely a cyclic factor depending on `x_[−s,s]`, shifted by
  `T^s`, grades the word graph at level `2s+1`.
- **Necessity (§2(1)).**
  - The factor idempotents `E_i` are cylinder polynomials of degree `≤ 3r−2` (sk-verify-14 F1; the relations used then have degree `≤ 6r−4`) satisfying `E_iE_j = δ_ij E_i`, `ΣE_i = 1`
    and `u E_i u^(-1) = E_(i±1)`.
  - A ring model keeps these relations, so the images are conjugate orthogonal idempotents with sum `I`, and `m | N`.
  - On the group side these relations are finitely many relators `e_12(p) = 1` of bounded length (cylinder words of
    `subshift-algebra-groups-embed-in-marked-groups`).
- **Sufficiency (§2(2)).**
  - Take a covering closed walk `C` at `v` and all large multiples of `g` as closed-walk lengths (Schur).
  - Walks `C·D` number at least `αΛ^(N−|C|)`; proper powers number at most `log_2(N)·βΛ^(N/2)`, with `Λ > 1` because
    `X` is infinite.
  - A non-power walk spells a primitive cyclic word with the same `(r+1)`-language.
  - Models and faithfulness below the wraparound radius come from the four-regular comparison.
- **Corollary.** Choose levels `r_k → ∞` with `g_(r_k) | N_k`.
