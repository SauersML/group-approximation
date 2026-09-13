---
rg: 2
id: dd-toeplitz-algebra-is-properly-infinite
kind: claim
title: The Pimsner-Toeplitz algebra of the Dixmier-Douady module is properly infinite (Blanchard's Question 5.4)
artifacts:
  - research/artifacts/lxi-dd-toeplitz-proper-infiniteness-2026-09-12.md
---

Let `E_DD` be the Dixmier--Douady Hilbert `C(B_∞)`-module over the complex Hilbert cube, with
infinite-dimensional fibres and every section vanishing somewhere, as in Blanchard,
arXiv:1507.02535v1, proof of Proposition 4.3. Its Pimsner--Toeplitz algebra `T(E_DD)` contains two
isometries with orthogonal ranges, so it is properly infinite. This answers Blanchard's Question 5.4
(1507.02535v1 and 1312.7722v7) positively. The same holds for the module `H~` of his (4.6), answering
Remark 5.3 a').

More generally: if `E = PF`, where `F` has `6n+2` orthonormal sections and `1-P` is the projection
onto `n` orthonormal sections, then `E ⊗ E` has two orthonormal sections, so `T(E)` is properly
infinite. The isometries are the creation operators `l(θ_1), l(θ_2)` of normalized Gram--Schmidt
combinations of `Σ_k P e_k ⊗ P e_k`. The Dixmier--Douady obstruction has codimension one in `E` and
disappears in `E ⊗ E`.

Relevance: by Blanchard--Rohde--Rordam Theorem 5.5, a unital `C(X)`-algebra with properly infinite
fibres that is not properly infinite would refute STW Problem LXI. Blanchard proposed these
Pimsner--Toeplitz fields of `O_∞` over infinite-dimensional spaces as the test case. This claim
closes both explicit candidates. It does not decide LXI, and modules whose deficiency is infinite at
every tensor power are untreated.
