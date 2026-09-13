---
rg: 2
id: arrangement-bnsr-invariants-avoid-real-resonance-citation
kind: route
title: Import Suciu's tropical upper bound for arrangements and the formality identity tau_1(V^q) = R^q
target: arrangement-bnsr-invariants-avoid-real-resonance
requires: []
---

Citation import. Read from the PDF of arXiv:2010.07499v2 (A. I. Suciu,
*Sigma-invariants and tropical varieties*, Math. Ann. 380 (2021)) on
2026-09-13.

- Theorem 13.3 (p. 26): "Let M be the complement of an arrangement of n
  hyperplanes in `C^l`. Then, for each `1 <= q <= l - 1`, the following hold.
  (1) `Trop(V^q(M))` is the union of a subspace arrangement in `R^n`.
  (2) `Sigma^q(M,Z) ⊆ S(Trop(V^q(M)))^c`."
- Section 13.1 (p. 25): Brieskorn's work implies that M is formal, "thus, by
  (43), we have that `tau_1(V^q(M)) = R^q(M)`, for all q."
- Section 1.2 (p. 2), recalling Proposition 2.7: "we always have an inclusion
  `tau_1^R(W) ⊆ Trop(W)`."

Combining: `S(R^q(M;R)) = S(tau_1^R(V^q(M))) ⊆ S(Trop(V^q(M)))`, so
`Sigma^q(M,Z)` avoids `S(R^q(M;R))`. For `P_n = pi_1` of the braid arrangement
complement in `C^n`, `l = n`; the homotopical `Sigma^q(P_n)` is contained in
`Sigma^q(M,Z)`.
