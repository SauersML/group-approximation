---
rg: 2
id: mf-two-generator-completeness-via-exact-switch-and-bridge
kind: route
title: Wrap the exact E switch in the two-generator bidirectional bridge
target: mf-recognition-two-generator-recursive-is-pi2-complete
requires:
  - exact-literal-e-fin-inf-switch
  - bidirectional-hnn-bridge-trivial-value-is-residually-finite
  - mf-recognition-recursive-presentations-is-second-level-complete
  - lef-recognition-has-a-pi2-upper-bound
  - lef-implies-operator-mf
  - mf-positive-controls
---

The exact switch has value `1` on `INF` and `E` on `FIN`.  The two-generator
bidirectional bridge is uniform, contains its input, and has residually
finite value on `1`.  Residually finite gives MF and LEF; containing `E`
refutes both.  The upper bounds are the two cited `Pi^0_2` normal forms.
