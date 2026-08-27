---
rg: 2
id: anchored-quantum-parallel-repetition-citation
kind: route
title: Import Bavarian--Vidick--Yuen anchored parallel repetition
target: anchored-quantum-parallel-repetition
requires:
  - anchoring-preserves-nonlocal-game-value
artifacts:
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

**Established by citation.**  Bavarian--Vidick--Yuen,
arXiv:1509.07466v2, Theorem 17, prove the dimension-sensitive statement; the
exponential value bound `(APR1)` is its immediate corollary, also stated as the
main theorem in the introduction.

The proof conditions a successful repeated strategy on a small set of won
coordinates, introduces dependency-breaking variables, uses quantum mutual
information and Pinsker/Uhlmann estimates to obtain question-local unitaries,
and rounds a random remaining coordinate to a one-copy strategy without
increasing local dimension.  Anchors provide a shared input at which the two
conditional states can be aligned; the accumulated estimates give the powers
`alpha^48` and `epsilon^17` in the stated bound.

Only the theorem is imported.  None of its quantum-information lemmas is
silently promoted to a group-relator or normalized-HS statement.
