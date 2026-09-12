---
rg: 2
id: noise-test-decodable-feature-transparency-proof
kind: route
title: Select a coordinate by the decoded class and read the shared right coordinate
target: noise-test-transparent-on-decodable-matching-features
requires: []
artifacts:
  - research/artifacts/unique-games-smooth-design-learnability-2026-09-11.md
---

Fix an optimal labeling `a(u,K)`, `beta(v)` of `Psi_c` and put
`F_u(x) = x_(a(u, D_u(x)))`, which is folded because `D_u` is shift invariant.

Condition on the right vertex `v` and neighbours `u,w`. The ideal outputs
`x_(a(u,K_(u,v)))` and `y_(a(w,K_(w,v)))` read right coordinates
`pi_(u,v)(a(u,K_(u,v)))` and `pi_(w,v)(a(w,K_(w,v)))`.

- If both coarsened edges are satisfied, both coordinates equal `beta(v)`, and
  the outputs agree with probability `1/m + (1-1/m) rho^3`: three symmetric
  kernels compose over a uniform symbol.
- Otherwise they agree with probability at least `1/m`.

Decoder failure moves either output with probability at most `e_c`.
Independence of `u` and `w` given `v`, regularity and Cauchy--Schwarz give the
square. The artifact (Section 2) has the full proof, the special cases and the
sandwich `val(Psi) <= val(Psi_c) <= val(UG_der(Psi))`. The argument is
self-contained and mathematical, with no proof-assistant verification.
