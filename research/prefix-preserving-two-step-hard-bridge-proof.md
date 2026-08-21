---
rg: 2
id: prefix-preserving-two-step-hard-bridge-proof
kind: route
title: First preserve the old prefix, then flip the fresh site sign
target: prefix-preserving-two-step-hard-bridge-localizes-exit
requires: []
---

Write `D_k=(I+B_k)/2` for `k<n` and `D_n^-=(I-B_n)/2`, so
`C_n=product_(k<n)D_k` and `X_n=C_nD_n^-`.

In the exact case, `(PPB4)` and `P_n<=C_n` give

```text
C_nu_nP_n=u_nP_n.
```

The first half of `(PPB1)` then gives `C_ns_nu_nP_n=s_nu_nP_n`.  For the
fresh sign,

```text
B_ns_nu_nP_n
 =s_na_nu_nP_n
 =s_nu_nA_nP_n
 =-s_nu_nP_n.
```

Hence `s_nu_nP_n` lies in both `C_n` and `D_n^-`, proving `(PPB5)`.

For the approximate estimate, telescoping a product of commuting contractions
gives

```text
||[C_n,W]||_2<=(1/2)sum_(k<n)||[B_k,W]||_2             (1)
```

for every unitary `W`.  Since `(I-C_n)P_n=0`,

```text
||(I-C_n)s_nu_nP_n||_2
 <=||[C_n,s_n]||_2+||[C_n,u_n]||_2.                    (2)
```

Also `A_nP_n=-P_n`, so

```text
||(I-D_n^-)s_nu_nP_n||_2
 =(1/2)||(I+B_n)s_nu_nP_n||_2
 <=(1/2)||B_ns_n-s_na_n||_2
   +(1/2)||a_nu_n-u_nA_n||_2.                          (3)
```

Because `C_n` commutes with `D_n^-`,

```text
I-C_nD_n^-=(I-C_n)+C_n(I-D_n^-).
```

Apply this identity to `s_nu_nP_n`, combine `(1)--(3)`, and obtain `(PPB6)`.
