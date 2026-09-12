---
rg: 2
id: maximally-entangled-vectorization-is-hs-isometry-proof
kind: route
title: Apply the vectorization identity and normalized Frobenius norm
target: maximally-entangled-vectorization-is-hs-isometry
requires: []
---

For column vectorization,

```text
(A tensor conjugate(B)) vec(I)=vec(A B^*).
```

Since `Phi_d=d^(-1/2)vec(I)` and
`||vec(C)||^2=Tr(C^*C)`, subtracting `Phi_d` gives `(MEH1)`.  If `A,B` are
unitary, right multiplication by `B` preserves normalized Hilbert--Schmidt
norm and

```text
||(A B^*-I)B||_2=||A-B||_2,
```

which gives `(MEH2)`.

