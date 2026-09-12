---
rg: 2
id: kazhdan-hyperbolic-b2-stability-via-ghb7-kernel
kind: route
title: Certify the congruence kernel of GHB_2(7) as a candidate and prove it flexibly HS stable
target: kazhdan-hyperbolic-b2-group-flexibly-hs-stable
requires:
  - ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
  - ghb7-congruence-kernel-flexibly-hs-stable
---

The kernel `H` of `ψ : G_{HB_2}(7) → SL_4(F_7)` is word-hyperbolic and Kazhdan with
`b_2(H;Q) >= 1380` (`ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2`, established).
If `H` is flexibly Hilbert--Schmidt stable (`ghb7-congruence-kernel-flexibly-hs-stable`, open),
then `H` witnesses the premise.

The only open input is the stability of one explicit, finitely presented group.
