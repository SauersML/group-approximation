---
rg: 2
id: zigzag-cyclic-shift-envelope-is-finitely-presented
kind: claim
title: The zigzag enumeration makes the cyclic Mallery-Zaremsky envelope an index-twelve subgroup of E_4
artifacts:
  - research/artifacts/boone-higman-zigzag-shift-compiler-2026-09-08.md
---

Use positive natural numbers and define nu:Z->N by

    nu(k)=2k+1 for k>=0,
    nu(k)=-2k for k<0.

For this enumeration, the Mallery-Zaremsky envelope E_nu(Z) has index
12 in E_4, the group of eventually 4-periodic permutations. In particular,
E_nu(Z) is finitely presented and strongly shift-similar. More precisely,
it is of type F_3 but not FP_4 (with integral coefficients).

This is a positive case of the explicit infinite-input shift compiler.
It does not establish that compiler for arbitrary finitely presented
decidable groups; Boone-Higman for Z was already known.

