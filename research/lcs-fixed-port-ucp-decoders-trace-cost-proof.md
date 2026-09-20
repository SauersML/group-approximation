---
rg: 2
id: lcs-fixed-port-ucp-decoders-trace-cost-proof
kind: route
title: Combine channel multiplicative defects with the finite conjugate trace bound
target: lcs-fixed-port-ucp-decoders-have-unbounded-trace-cost
requires:
  - lcs-auth-three-controls-lose-common-corner-weight
artifacts:
  - research/artifacts/lcs-fixed-port-ucp-trace-cost-2026-09-20.md
  - research/artifacts/lcs-auth-proper-corner-audit-2026-09-20.md
---

Use the explicit family and finite disjoint-conjugate trace calculation
proved in the prerequisite's artifact. Its centered conjugate average
D satisfies tr(R_m(D)^2)<=3/(16N)+9 beta_N^m/16.

The new artifact supplies a finite-dimensional dilation proof that a
port with variance eta^2 changes the decoded state by at most 2 eta
under conjugation of any contraction. Telescoping along conjugator
words bounds the decoded average of b by phi_m(R_m(b))+2 L_N eta_m.
State Cauchy--Schwarz and the density bound phi_m<=C_m tr then give
the displayed finite inequality. A bounded subsequence of C_m would
force 1<=3C/N for every N, a contradiction.

If the port images are exact unitaries the same dilation calculation
makes them multiplicative-domain elements. Literal controlled-U_0
semantics then annihilate b for any decoded projection. No reducing
corner hypothesis is used and no inference to arbitrary replacement
ports is made.
