---
rg: 2
id: conjugacy-orbit-version-of-the-endpoint-bound-proof
kind: route
title: Apply the endpoint estimate in every global frame
target: head-retention-forces-distance-from-every-global-frame
requires:
  - head-retention-forces-macroscopic-carrier-motion
---

Fix a unitary `W` and define the conjugated carrier

```text
A_s^(W)=W A_s W^*.
```

For every word `q`,

```text
q(A^(W))=Wq(A)W^*.
```

In particular the top endpoint relator and the bottom head remain
unitarily conjugate in the represented finite group, and all normalized
Hilbert--Schmidt distances used in
`word-telescoping-transfers-the-endpoint-conjugacy-proof` are unchanged.
Applying that proof with `A^(W)` in place of `A` gives

```text
||w(U)-I||_2
 <= C_0 delta(U)+C_1 max_s||U_s-WA_sW^*||_2.           (CGO1)
```

The constants are the same for every `W`. Taking the infimum over all
unitaries proves `(HGF2)`.

If `U_s=WA_sW^*` exactly, then `eta_orb(U,A)=0` and `(HGF2)` recovers the
original endpoint firewall. More generally a sequence with positive head
and vanishing presentation defect has

```text
liminf eta_orb(U,A) >=
 liminf ||w(U)-I||_2/C_1.
```

Hence common frame motion, no matter how large its rotation angle, cannot
be the continuous two-sheet escape. Only relative motion between
generators remains.
