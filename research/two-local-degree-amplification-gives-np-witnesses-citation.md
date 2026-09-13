---
rg: 2
id: two-local-degree-amplification-gives-np-witnesses-citation
kind: route
title: Import Brandao--Harrow Corollary 11 on degree-amplifying quantum maps
target: two-local-degree-amplification-gives-np-witnesses
requires: []
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
---

Literature import. Brandao--Harrow, arXiv:1310.0017v2, read on 2026-09-12.

- Corollary 11 (v2 PDF p. 9) lists hypotheses (i)--(vii) and concludes "Then the
  quantum PCP conjecture is false."
- Its proof (Section 6, TeX `sec:proofCSPs`) pads the input to degree `D`, which
  scales the NO energy to at least `eps/D`. It then applies `P_t` and uses
  Corollary 5 to estimate `e_0(P_t(H'))` to accuracy
  `12(d^(2t) ln(d^t)/D^t)^(1/3)` with an NP witness of size `n^(O(t))`. With
  `D=8d^3` this accuracy is at most `12*2^(-t)`, and `t>=log_2(96d^3/eps)`
  separates the cases. The proof ends: "our original energy estimation problem is
  in NP, which implies the quantum PCP theorems is false (assuming that
  NP != QMA.)"

The regularity reading of hypothesis (iii) and the discretization remark are
recorded in the claim. Section 1 of the linked artifact quotes the source.
