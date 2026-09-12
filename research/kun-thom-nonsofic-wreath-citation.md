---
rg: 2
id: kun-thom-nonsofic-wreath-citation
kind: route
title: Import the Kun--Thom wreath theorems from the verified preprint
target: kun-thom-nonsofic-wreath
requires: []
---

Citation import, not a reproof.  The statements of Theorems A, C, E and
Corollary D were read from the PDF of arXiv:2608.06222v1 on 2026-08-14 by
the literature scout, using `pdftotext` after an arXiv HTML render returned
demonstrably wrong content for the same paper.

The proof of Theorem A runs: Kun's expander decomposition
(arXiv:1606.04471v5, Theorem 1) applied to the `Gamma`-labels of a sofic
approximation, the Kun--Thom single-expander obstruction
(arXiv:1901.03963v3, Theorem 1.1), and the infranormality hypothesis to
match transported components injectively.  Nonsoficity of the wreath then
follows from the failure of the coset action to be sofic.

This route asserts only that the cited theorems say what this graph records
them as saying.  It does not assert that the repository's own wreath
candidate satisfies their hypotheses — that identification is the open
content of `wreath-not-sofic`.
