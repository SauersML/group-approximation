---
rg: 2
id: toeplitz-parity-balanced-regularization-proof
kind: route
title: Retain the negative sign while Diracizing the old character
target: toeplitz-parity-surviving-corner-is-canonically-regularizable
requires:
  - toeplitz-parity-negative-corner-has-trivial-scalar-kernel
  - central-involution-corner-exactification
---

After passing to a subsequence, normalized coordinate traces converge
pointwise on `Lambda` to a character `tau`. The scalar-kernel theorem gives

```text
|tau(g)|<1              for every 1!=g in Lambda.       (TPR3)
```

Choose the subsequence and `k_n->infinity` diagonally so that

```text
(2k_n+1) epsilon_n(F_n)->0
```

on exhausting relator windows and so that the first `n` trace values are
sufficiently close to their limits.

For a relator evaluation `A`, telescoping tensor factors gives

```text
||A tensor (A tensor bar(A))^(tensor k)-I||
 <=(2k+1)||A-I||.                                       (TPR4)
```

This holds in operator norm and normalized Hilbert--Schmidt norm. Thus
`(TPR1)` remains asymptotically multiplicative. Its trace is

```text
tr(V_n(g))
 =tr(U_n(g)) |tr(U_n(g))|^(2k_n)+o(1).                  (TPR5)
```

Equation `(TPR3)` makes `(TPR5)` tend to zero for every nonidentity
`g in Lambda`. For `J`, the retained factor contributes `-1` and every
conjugate pair contributes `+1`, so `V_n(J)=-I` exactly.

Finally

```text
tr_ad(Ad(V_n(g)))=|tr(V_n(g))|^2->delta_(g,1).
```

Hence every polynomial moment of the adjoint Markov operator converges to
the regular walk. Nonamenability of `Lambda` can be read from its quotient
through

```text
T -> F_2[z,z^(-1)];
```

no Kazhdan theorem is needed. Kesten and Portmanteau give the asserted
low-energy-density conclusion.
