---
rg: 2
id: fanizza-compression-implies-localized-square-return
kind: route
title: Square the compressed verifier reflection and discard the verifier payload
target: localized-square-return-wandering-promotion
requires:
  - fanizza-coherent-verifier-wandering-promotion
---

**INVALIDATED BY `uniform-clock-corner-is-not-a-reflection`.** The proposed
argument used the group, carrier `Q`, and ordinary word `w` from the coherent
Fanizza promotion and then asserted

```text
||Q_U w(U) Q_U-Q_U V_m(U)Q_U||_2=o(1),
(Q_U V_m(U)Q_U)^2=Q_U.
```

The second line is false for the established controlled-clock reflection.
The correct identities are

```text
Q_U V_m(U)Q_U=(1-H_m(U))Q_U,
Q_U V_m(U)(1-Q_U)V_m(U)Q_U=H_m(U)(2-H_m(U))Q_U.
```

Thus squaring returns through the complementary carrier, and the leakage is
generally positive. The finite-order compression telescope cannot be
invoked. A new reducing carrier or a separate excursion-control theorem
would be required to obtain the localized square return.
