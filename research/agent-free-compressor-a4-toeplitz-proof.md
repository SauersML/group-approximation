---
rg: 2
id: agent-free-compressor-a4-toeplitz-proof
kind: route
title: Amalgamate the injected three-cycle and telescope the triangle relators
target: agent-free-compressor-a4-toeplitz-root-compiler
requires:
  - schur-toeplitz-root-mark-is-fd-invisible
---

The coefficient embedding in
`schur-idempotent-is-an-injective-toeplitz-defect` keeps `P_f!=0`, so root
injectivity in the Steinberg group gives `w_f!=1`.  Root additivity in
characteristic three gives `w_f^3=1`; hence `<w_f>` is an injected `C_3`.
The element `z` in `(ATC2)` is a three-cycle and also generates an injected
`C_3`.  The normal-form theorem for free products with amalgamation proves
that both vertex groups embed in `(ATC3)`, so `b!=1`.

For the ultraproduct assertion, restrict a homomorphism on `G_ATC` to
`H_f`.  The assumed Toeplitz root-collapse theorem gives `w_f=1`, and the
edge relation gives `z=1`.  The triangle relators reduce to `b^2=b^3=1`,
hence `b=1`.

For `(ATC5)`, fixed-word telescoping first bounds `||z-w_f||_2`.  Replacing
the three occurrences of `z` in `(bz)^3` by `1` costs at most
`3||z-1||_2`, so `||b^3-1||_2` is bounded by that quantity and the triangle
relator defect.  Finally

```text
b-1=(b^3-1)b^(-2)+b(1-b^(-2)),
```

and the second term is controlled by `||b^2-1||_2`.  This proves the fixed
dimension-independent bound.

For conservativity, the quotient of `(ATC2)` by `b=1` is `C_3`, proving that
every `C_3` representation extends.  The restriction identity follows either
from cosets or from the regular-character formula
`Reg(A4)|C_3=[A4:C_3]Reg(C_3)`.
