---
rg: 2
id: exterior-tensor-powers-asymptotically-free-proof
kind: route
title: A free orbit, polynomial interpolation and projectivity split the regular module off an exterior tensor power, and expansion makes the free proportion tend to one
target: exterior-tensor-powers-are-asymptotically-free
requires: []
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/fock-local-rank-models-2026-09-12.md
---

Section 1 of the artifact: Lemma 1.1, Theorem 1.2, Corollaries 1.3–1.4.

1. **Free orbit.** A basis tuple of `W*` in `(W*)^(⊕w)` has trivial stabilizer, since `Γ` is faithful.
2. **Interpolation.** Every function on a finite subset of `F_q^N` is a polynomial of degree
   `<= N(q−1)`. Restricting polynomial functions of bounded degree to the orbit gives a surjection onto
   `F_qΓ`.
3. **Splitting.** The source is a quotient of a summand of `(F_q ⊕ W^(⊕w))^(⊗D)`, which is itself a
   summand of `Λ(W)^(⊗wD)` (multidegree at most one per copy). `F_qΓ` is projective, so the surjection
   splits.
4. **Expansion.** With `Λ(W)^(⊗r) = F_qΓ ⊕ R`, `(F_qΓ ⊕ R)^(⊗s)` is free except for `R^(⊗s)`, because
   `F_qΓ ⊗ Y` is free.
5. **Conjugation.** Two actions on the same space whose free parts have codimension `<= δD` share a free
   submodule of codimension `<= δD`. Matching it gives an `X` with rank error `<= δD`.

*Verification by `w3-vf-linear` (2026-09-12), Section 28.1 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. Recomputed: the free orbit of a dual basis tuple, degree bound w^2(q−1), splitting onto projective F_qΓ, the degree-<=1 summands giving r = w^3(q−1), the expansion bound (1−η)^s, the Corollary 1.3 intertwiner, and injectivity through fixed spaces |Γ|/ord a.*
