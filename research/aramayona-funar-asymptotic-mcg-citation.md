---
rg: 2
id: aramayona-funar-asymptotic-mcg-citation
kind: route
title: Import the exact sequences, finite presentability and perfection of the Aramayona--Funar groups, and the type F-infinity theorem of Aramayona--Bux--Flechsig--Petrosyan--Wu
target: aramayona-funar-asymptotic-mcgs-are-fp-extensions-of-v
requires: []
artifacts:
  - research/artifacts/bh-mcg-closed-surface-2026-09-12.md
---

Citation import. The sources are as in the target.
- **AF**, arXiv:1701.08132v2, pages 1--12: Theorem 1.2, Corollary 1.5, Theorems
  1.11 and 1.13, Lemmas 2.1 and 2.2, Proposition 4.2, Lemma 4.4, Corollary 4.5
  and Proposition 4.6.
- **ABFPW**, arXiv:2110.05318v5, pages 1--5: Theorems 1.1, 1.5 and 1.7, sequence
  (1.3) and the identifications on page 5.

The PDFs were downloaded on MSI on 2026-09-12. MSI's python has no `pypdf`, so
there was no text extraction; each quoted page was read as a page image.

Not reproved here, and there is no Lean counterpart. The proofs were not
checked:
- finite presentability, AF Section 5, via Brown's criterion on a reduced pants
  complex;
- type `F∞`, ABFPW Sections 5, 6 and 9.
