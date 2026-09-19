---
rg: 2
id: affine-leavitt-p-heisenberg-hs-transfer-proof
kind: route
title: Transfer native root collapse through one odd Heisenberg character average
target: affine-leavitt-p-heisenberg-hs-corner-blocker
requires:
  - affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner
  - affine-leavitt-steinberg-hs-coefficient-decoder
  - approximate-relative-leavitt-cell-kills-active-trace
---

Apply the decoder and the relative-Leavitt trace inequality to obtain
`(PHB2)`.  For unitaries `W,Z`, telescoping gives

```text
||W Z W^* Z^*-I||_2 <=2||W-I||_2.                       (PHT1)
```

The defect of the fixed Heisenberg relator adds at most `delta`, proving
`(PHB3)`.  For every `k`,

```text
||C^k-I||_2 <=k||C-I||_2.                               (PHT2)
```

Insert `(PHT2)` into the zero-sum Fourier expansion `(PHB4)`.  Left
multiplication by the binary packet factor has operator norm at most one,
so `(PHB5)` follows.
