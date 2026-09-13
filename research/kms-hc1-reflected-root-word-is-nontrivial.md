---
rg: 2
id: kms-hc1-reflected-root-word-is-nontrivial
kind: claim
title: A reflected root word has infinite order in an explicit hyperbolic Kazhdan KMS group
artifacts:
  - research/artifacts/kms-hc1-marked-root-kernel-candidate-2026-09-12.md
---

For every prime `p>=7`, let `Gamma_p` have presentation

```text
< a,b,c |
  a^p, b^p, c^p,
  [a,b,a], [a,b,b], [b,c,b], [b,c,c],
  [a,c,a], [a,c,c,a], [a,c,c,c] >,
```

where `[x,y]=x^-1 y^-1 x y` and iterated commutators associate to the
left. Then `Gamma_p` is an infinite word-hyperbolic Kazhdan group and

```text
r_p=[b,a],   s_p=[b,c],   w_p=(r_p s_p)^p
```

satisfy `<r_p,s_p> = <r_p>*<s_p> = C_p*C_p`. In particular `w_p` has
infinite order.

Moreover, `w_p` lies in the kernel of the canonical map from `Gamma_p`
to the positive subgroup of the corresponding minimal Kac--Moody group
over `F_p`. This last kernel statement is not a statement about every
finite quotient of `Gamma_p`.
