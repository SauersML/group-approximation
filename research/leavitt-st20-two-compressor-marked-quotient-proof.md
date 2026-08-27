---
rg: 2
id: leavitt-st20-two-compressor-marked-quotient-proof
kind: route
title: Pull the LEF elementary model back through the Steinberg projection
target: leavitt-st20-two-compressor-mark-is-mf-visible
requires:
  - leavitt-two-compressor-core-is-lef-and-marked-operator-mf
---

The canonical projection

```text
St_20(L_(F_2)(1,2)) -> EL_20(L_(F_2)(1,2))
```

sends the diagonal root packet and the two chosen Whitehead words onto the
generators of the elementary two-compressor core `B_EL`.  Its restriction
therefore gives a surjection

```text
pi:B_Delta -> B_EL.
```

The marked Steinberg root maps to the nonidentity elementary transvection
`e_13(s_1t_1)`.  By the prerequisite, `B_EL` has an injective homomorphism
`iota` into a norm matrix corona.  The composite `iota o pi` is a
homomorphism from `B_Delta` to that corona and its value on `z` is nonidentity.
Thus `z` is not in the MF radical of the chosen Steinberg core.
