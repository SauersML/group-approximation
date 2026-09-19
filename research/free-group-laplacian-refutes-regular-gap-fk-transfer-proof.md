---
rg: 2
id: free-group-laplacian-refutes-regular-gap-fk-transfer-proof
kind: route
title: Add one superexponentially small character eigenvalue to mean-zero finite-quotient models
target: free-group-laplacian-refutes-regular-gap-fk-transfer
requires: []
---

Residual finiteness supplies finite quotients `q_n:F_2->Q_n` injective on
growing balls. Their regular representations are exact regular-character
microstates, but the constant vector lies in the kernel of `L`.

For an invertible version, let `pi_n=lambda_(Q_n)|_(1^perp)`. The finite Cayley
graph is connected, so `L(pi_n)>0`. If a fixed nontrivial word survives in
`Q_n`, then

```text
Tr(pi_n(w))=-1,
```

because `lambda_(Q_n)=1 direct_sum pi_n`; hence the normalized characters of
`pi_n` still converge to the regular character.

Add the one-dimensional character

```text
chi_epsilon(a)=exp(i epsilon),        chi_epsilon(b)=1.
```

On this line `L=2-2 cos(epsilon)>0`. Write
`B_n=log det L(pi_n)` and `D_n=dim(pi_n direct_sum chi_epsilon)=|Q_n|`.
Choose `epsilon_n>0` so small that

```text
log(2-2 cos(epsilon_n)) <= -D_n^2-|B_n|.
```

Then `sigma_n=pi_n direct_sum chi_(epsilon_n)` is exact, remains a
regular-character microstate, and has invertible `L(sigma_n)`, while its
normalized log determinant is at most `-D_n`.
