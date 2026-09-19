---
rg: 2
id: involutory-opposite-root-transfer-proof
kind: route
title: Delete the conjugated square and commute through the remaining Weyl word
target: involutory-opposite-root-face-obeys-projective-transfer
requires: []
---

Unitary invariance of normalized Hilbert--Schmidt norm gives

```text
||H b^(-2) H^*-I||_2=||b^(-2)-I||_2=||b^2-I||_2=beta.
```

Starting from `R`, replace the leading `a^2` by `I` at cost `alpha` and the
conjugated `b^(-2)` by `I` at cost `beta`. Therefore

```text
||H-a b a^*||_2<=eta+alpha+beta.                         (IOP1)
```

For any two unitaries `H,K`,

```text
||UH-HU||_2<=2||H-K||_2+||UK-KU||_2.                    (IOP2)
```

Take `K=aba^*`. Moving `U` successively across `a`, `b`, and `a^*`
costs at most

```text
||Uaba^*-aba^*U||_2<=2 epsilon_a+epsilon_b.              (IOP3)
```

Combining `(IOP1)--(IOP3)` proves the corresponding bound for
`||UH-HU||_2`. Finally

```text
||UHU^*H^*-I||_2=||UH-HU||_2,
```

which is `(IOR2)`.

