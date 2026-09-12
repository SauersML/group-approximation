---
rg: 2
id: multi-piece-triangular-lift-gives-left-invertible-s0-lift
kind: route
title: An acyclic defect graph makes the product of the piece lift pair one plus a nilpotent, so the lift of s0 is left invertible
target: left-invertible-lift-of-s0-in-leavitt-group-algebra
requires:
  - finite-support-multi-piece-triangular-s0-lift-exists
artifacts:
  - research/artifacts/triangular-lift-hnn-transfer-2026-09-12.md
---

Artifact Lemma 4.1.
- `b a = 1 + sum X_ij`, with `b = sum E_i[g_i^(-1)]`.
- An acyclic defect digraph makes `sum X_ij` strictly triangular in Peirce form, so `b a` is a unit.
- `(b a)^(-1) b` is a left inverse of `a`, and `pi(a) = s0`, which is not invertible.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 27 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. Checked:*
- *`X_ij X_kl = 0` unless `j = k`, so `N^m` sums directed paths of length `m`, and these vanish for an acyclic digraph on `m` vertices;*
- *`π(a) = s_0` holds cylinder by cylinder.*
