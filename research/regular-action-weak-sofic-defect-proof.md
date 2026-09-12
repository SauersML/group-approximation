---
rg: 2
id: regular-action-weak-sofic-defect-proof
kind: route
title: Translation has no fixed points, so its Hamming length is discrete
target: regular-action-makes-weak-sofic-defects-maximal
requires: []
artifacts:
  - research/artifacts/weak-soficity-surjunctivity-route-2026-09-12.md
---

Theorem A of the artifact. If `zv = v` for some `v` in `H`, then `z = 1` after
cancelling `v` on the right. So `fix(z) = 0` for every `z != 1`, giving
`l_V(z) = 1`, and `fix(1) = |H|` gives `l_V(1) = 0`.

For the consequence, Lemma 1.1 of the artifact shows that the transported
identity holds at `v` as soon as `phi(n)phi(m)v = phi(nm)v` for the memories
`N` of the decoder and `M` of the encoder. The set of `v` where that fails for
a fixed pair is the complement of the fixed set of the defect
`phi(n)phi(m)phi(nm)^-1`, of normalized size exactly `l_V` of that defect. By
the displayed computation that size is `1` for a nontrivial defect, so the
identity fails at every vertex unless the defect is trivial. A union bound over
the finitely many pairs gives the stated form.

The proof is complete and uses no hypothesis on the length `l`, which is why
the conclusion holds for every weakly sofic approximation.

**Verified 2026-09-12** by gk-vf-positive, independent re-derivation: PASS (Section 8.1 of `research/artifacts/gk-vf-positive-verification-2026-09-12.md`). Correction: "so the identity fails at every vertex unless the defect is trivial" should read "so Lemma 1.1 guarantees the identity at no vertex unless the defect is trivial".
