---
rg: 2
id: signed-monomial-hs-hamming-comparison-proof
kind: route
title: Double every signed coordinate and compare Hamming with Hilbert--Schmidt distance
target: signed-monomial-tracial-images-are-sofic
requires: []
---

It suffices by bi-invariance to compare `U in B_d` with the identity.  Write

```text
a=#{i:sigma(i)=i and epsilon_i=+1},
b=#{i:sigma(i)=i and epsilon_i=-1},
c=d-a-b.                                                (SMH1)
```

In the doubled-set action `(SMT2)`, precisely the `2a` points above the
positive fixed coordinates are fixed.  Hence

```text
d_H(j_d(U),1)=(b+c)/d.                                  (SMH2)
```

On the other hand `Re Tr(U)=a-b`, so

```text
(1/2)||U-1||_(2,d)^2
 =1-Re tr_d(U)
 =(c+2b)/d.                                             (SMH3)
```

Equations `(SMH2)--(SMH3)` prove `(SMT3)`.  In particular a sequence is
HS-trivial exactly when its doubled signed action is Hamming-trivial.
Multiplication is preserved because every `j_d` is a homomorphism.  After
quotienting by the common identity kernel, `(SMT4)` follows.
