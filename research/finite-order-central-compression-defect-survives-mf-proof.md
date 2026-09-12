---
rg: 2
id: finite-order-central-compression-defect-survives-mf-proof
kind: route
title: Build the compressed cyclic action from clock, shift, and multiplier matrices
target: finite-order-central-compression-defect-survives-mf
requires: []
---

Let `n` run through the odd positive integers and put

```text
omega_n=exp(2 pi i/n),             m_n=(n+1)/2.
```

On `C^n`, indexed by `j in Z/nZ`, define

```text
U_n e_j=omega_n^j e_j,
X_n e_j=e_(j+1),
T_n e_j=e_(m_n j).
```

Because `2m_n=1 mod n`, `T_n` is a permutation unitary and direct evaluation
on the standard basis gives

```text
U_n X_n=omega_n X_n U_n,
T_n U_n T_n^*=U_n^2,
T_n X_n T_n^*=X_n^(m_n).                         (FC1)
```

On `C^n (+) C^n`, set

```text
A_n=diag(U_n,U_n),
B_n=diag(T_n,T_n),
C_n=[[0,X_n],[X_n^*,0]].                         (FC2)
```

These are unitaries, `C_n^2=I`, and `(FC1)` yields

```text
B_n A_n B_n^*=A_n^2,
||A_n C_n-C_n A_n||=|omega_n-1| -> 0.             (FC3)
```

Let `a,t,c` be their classes in

```text
Q=prod_n M_(2n)(C) / direct-sum_n M_(2n)(C),
```

and let `G` be the subgroup of `U(Q)` they generate. Then `G` is countable
and MF by construction, while `(FC3)` gives

```text
tat^(-1)=a^2,             c^2=1,             [a,c]=1.   (FC4)
```

For every fixed nonzero integer `k`, the order of the roots occurring in the
spectrum of `U_n^k` is `n/gcd(n,k)`, which tends to infinity. Therefore

```text
||A_n^k-I|| -> 2.                                      (FC5)
```

Thus `a` has infinite order. In particular `<a^2>` is a proper subgroup of
`<a>`, and `(FC4)` says that `t` properly compresses `<a>`.

It remains to calculate the compression defect. Put

```text
V_n=B_n C_n B_n^*
   =[[0,X_n^(m_n)],[X_n^(-m_n),0]].                    (FC6)
```

For the commutator convention `[x,y]=xyx^(-1)y^(-1)`, `(FC1)` gives

```text
[V_n,A_n]
 =diag(omega_n^(-m_n) I_n, omega_n^(m_n) I_n).         (FC7)
```

But

```text
omega_n^(m_n)=-exp(pi i/n),
omega_n^(-m_n)=-exp(-pi i/n).
```

Hence `||[V_n,A_n]+I|| -> 0`, and so in `Q`

```text
[tct^(-1),a]=-I.                                      (FC8)
```

This element is central, has order two, and is nonidentity. It belongs to
the compression-centralizer defect by its displayed form. Since its
operator-norm and normalized-Hilbert--Schmidt displacement from the identity
are both two, the example also fences attempts to repair unrestricted
transport merely by making a torsion defect macroscopic.

The identities were additionally checked as exact monomial-matrix identities
in dimensions `2n` for `n=3,5,7,9,11,25`; the proof itself is the symbolic
calculation above and does not depend on those finite checks.
