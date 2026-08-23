---
rg: 2
id: or3-proper-corner-rank-firewall-proof
kind: route
title: Use the oriented OR3 support as the missing proper-corner rank
target: or3-fixed-proper-corner-return-hits-regular-firewall
requires:
  - raw-prefix-covariance-reduces-to-nonincidence-cap-commutators
  - canonical-b7-or3-corner-defeats-finite-prefix-actors
  - full-support-factor-refutes-exact-exhaustive-typed-cap-chain
  - universal-block-return-violates-the-regular-firewall
  - functorial-packet-return-firewall
---

Because `D=DE`, its right support `H=supp(D^*D)` lies below `E`.  The
compression `X=FUE`, `F=E-H`, has final support of trace at most `tau(F)`.
Polar equivalence gives the same trace bound for its initial support.  At
least `tau(H)` of `E` is therefore in the kernel of `X`, on which the Gram
deficiency is exactly `-E`.  This proves the second half of `(OPC2)`; the
first follows from contractivity of the projection-product commutator `D`.

In the exact artifact `D=|e_4><e_0|`, so `D^*D=e_0` and `(OPC3)` follows.
For `U=1`, `X=e_1` and `X^*X-E=-e_0`, proving sharpness.  Multiplying its
ordinary trace-one value by the canonical B7 block factor `7/645120` gives
`(OPC4)`.

Finally evaluate a purported exact source-fullness identity in the regular
finite von Neumann algebra.  The same support computation gives `H=0`.
Faithfulness turns this into algebraic death of the oriented source, while
the exhaustive cap-chain firewall rules out that death in the supplied
full-support completion.  This proves the proper-corner dichotomy.

