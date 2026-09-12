---
rg: 2
id: mf-safe-compiler-via-product-commuting-aanderaa-cohen
kind: route
title: Run the product-commuting Aanderaa-Cohen compiler on the two-generator bridge
target: mf-safe-finite-presentation-compiler
requires:
  - product-commuting-aanderaa-cohen-compiler
  - c-free-aanderaa-rope-is-mf-with-fine-quotients
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
  - exact-literal-e-fin-inf-switch
---

Feed `C = B2(S_e)` to the product-commuting compiler.  On `INF`, `C = B2(1)`
is residually finite and `H_3''` is MF by the amalgamated-base twisted-edge
theorem once the `C`-free rope satisfies `(CF1)`; on `FIN`, `E <= C <=
H_3''`.
