---
rg: 2
id: product-states-approximate-high-degree-2-local-citation
kind: route
title: Import the Brandao--Harrow product-state approximation for high-degree 2-local Hamiltonians
target: product-states-approximate-high-degree-2-local
requires: []
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
---

Literature import. Brandao--Harrow, *Product-state approximations to quantum
ground states*, arXiv:1310.0017v2. Theorem numbers were read from the v2 PDF
(pp. 6--9), and statements from the v2 TeX source, on 2026-09-12:

- Theorem 3: for any `n`-qudit state on a `D`-regular graph there is a globally
  separable state with average edge trace distance at most
  `12(d^2 ln(d)/D)^(1/3)`;
- Corollary 4: (PS1) for `H=E_((i,j) in E) H_ij`, `||H_ij||<=1`;
- Corollary 5: witnesses of length `O(nd log(n/delta))` when
  `beta-alpha>=12(d^2 ln(d)/D)^(1/3)+delta`, verifier time `nDd^4 polylog(1/delta)`;
- Section 2.1.4: the `k>2` remark and the gadget remark quoted in the claim.

The claim's degree threshold is the arithmetic `12(d^2 ln d/D)^(1/3) >= gamma`
if and only if `D <= 1728 d^2 ln(d)/gamma^3`. Section 1 of the linked artifact
records the source reading.
