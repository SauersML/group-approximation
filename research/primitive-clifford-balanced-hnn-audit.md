---
rg: 2
id: primitive-clifford-balanced-hnn-audit
kind: route
title: Express the source and target as signed C2-cubed Reynolds atoms
target: primitive-clifford-balanced-atoms-have-hnn-obstruction
requires:
  - primitive-clifford-type-fixes-orientation-not-return
  - finite-character-idempotents-have-exact-hnn-transport
---

On `Z_1=-1`, the operator `CZ_2` is identically `+1`; changing controller
orientation makes it identically `-1`.  This proves `(PBA3)`.  The usual
three commuting sign cuts prove `(PBA5)`, and the map `(PBA6)` preserves the
characters, so ordinary HNN covariance transports the signed averages.

If the transporter also obeyed `WZ_1W^*=t`, its image of `p_s` would lie in
the negative spectral projection of `t`.  The `fz_-` half of `p_t` lies in
the positive spectral projection instead and has regular trace `1/16`.
This proves the literal HNN obstruction.
