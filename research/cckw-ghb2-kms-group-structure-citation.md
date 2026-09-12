---
rg: 2
id: cckw-ghb2-kms-group-structure-citation
kind: route
title: Import Caprace--Conder--Kaluba--Witzel Theorems 1.3 and 3.1 and Propositions 7.2 and 7.15 for GHB_2(7)
target: cckw-ghb2-kms-group-structure
requires: []
---

Citation import, not a reproof.

P.-E. Caprace, M. Conder, M. Kaluba, S. Witzel, *Hyperbolic generalized triangle groups,
property (T) and finite simple quotients*, arXiv:2011.09276. Downloaded from arXiv on
2026-09-12 and read from ghostscript text extraction on MSI
(`/scratch.global/sauer354/hs-cand/cckw2.txt`):
- Theorem 1.3 and its display of `G_{HB_2}(p)`;
- Theorem 3.1 (i)–(v) with its proof sketch;
- the half-girth type `(3,4,4)` of `G_{HB_2}(p)`;
- Propositions 7.2 and 7.15.
Quotes are in `research/artifacts/ghb7-kernel-certified-candidate-2026-09-12.md`.

Verification boundary:
- **Not re-read:** the proofs of Theorem 1.3 and of Theorem 3.1 (i), (ii), (v). CCKW cite
  Bridson--Haefliger II.12.28 for the latter.
- **Minus signs:** the extraction lost minus signs in the Proposition 7.15 matrices. The
  compiled `decide +kernel` relator checks in `Kazhdan/GHBQuotientMatrices.lean` fix the
  exact matrices.
- **Corroborated by compiled Lean:** property (T), vertex injectivity of `ψ`, and the link
  girths.

This route asserts only that the source says what the claim records.
