---
rg: 2
id: msz-clifford-machine-skeleton-citation
kind: route
title: Import the MSZ HNN normal form and polynomial-filling host
target: msz-clifford-machine-skeleton-has-polynomial-fillings
requires:
  - quantitative-higman-embedding-with-dehn-control
artifacts:
  - research/artifacts/mehta-slofstra-zhao-positivity-ingestion-2026-08-20.md
---

**Established by citation.** In Mehta--Slofstra--Zhao,
arXiv:2312.05617v2, Lemma 4.6 gives the six generators and the displayed
addressing formulas.  The presentation immediately following that lemma
gives `(MCS2)`.  Proposition 4.7 proves deterministic polynomial-time word
problem by central-product normal forms and Britton reduction.  Proposition
4.8 applies BORS and then replaces the remaining generators by products of
two involutions, obtaining `(MCS3)`.

The dependency on `quantitative-higman-embedding-with-dehn-control` records
the stronger modern BORS interface already imported in Cairn.  The cited MSZ
proof itself uses the original BORS exponent.
