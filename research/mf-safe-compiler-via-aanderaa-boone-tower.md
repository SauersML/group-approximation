---
rg: 2
id: mf-safe-compiler-via-aanderaa-boone-tower
kind: route
title: Run the Aanderaa compiler on the two-generator bridge with an MF Boone engine
target: mf-safe-finite-presentation-compiler
requires:
  - boone-group-is-mf
  - aanderaa-rope-layers-are-mf-safe
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
  - exact-literal-e-fin-inf-switch
---

Feed `Gamma_e = B2(S_e)` (two-generator bridge of the exact switch) to the
Aanderaa compiler.  On `INF`, `Gamma_e = B2(1)` is residually finite and the
engine plus rope layers keep `G_7` MF; on `FIN`, `E <= Gamma_e <= G_7`.  This
is an alternative to the benign-witness rope route, with all edge groups free.
