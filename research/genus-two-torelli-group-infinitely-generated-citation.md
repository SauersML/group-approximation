---
rg: 2
id: genus-two-torelli-group-infinitely-generated-citation
kind: route
title: "Import the genus two Torelli group as an infinitely generated free group from Mess, McCullough-Miller and BBM"
target: genus-two-torelli-group-infinitely-generated
requires: []
---

Citation import, not a reproof. Sources read on 2026-09-13 from the arXiv PDFs:

- M. Kassabov, A. Putman, *Equivariant group presentations and the second homology
  group of the Torelli group*, Math. Ann. 376 (2020), arXiv:1807.01338v3, §1,
  pages 1–2, verbatim: "McCullough–Miller [McCuMi] proved that I_2^b is not even
  finitely generated. Mess [Me] strengthened this by showing that I_2 is an infinite
  rank free group."
- M. Bestvina, K.-U. Bux, D. Margalit, *The dimension of the Torelli group*,
  arXiv:0709.0287v1, **Theorem A** (page 1), verbatim: "For g ≥ 2, we have
  cd(I(S_g)) = 3g − 5." Abstract, verbatim: "For g ≥ 2, we prove that the top
  dimensional homology of the Torelli group is infinitely generated. Finally, we give
  a new proof of the theorem of Mess that gives a precise description of the Torelli
  group in genus 2."

Consistency check of the import: at `g = 2`, Theorem A gives `cd(I_2) = 1`, so
`I_2` is free (Stallings–Swan). The top-dimensional homology is `H_1(I_2; Z)`,
infinitely generated, so the free group has infinite rank.
