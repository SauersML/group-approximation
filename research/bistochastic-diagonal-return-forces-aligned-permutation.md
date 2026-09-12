---
rg: 2
id: bistochastic-diagonal-return-forces-aligned-permutation
kind: claim
title: A square bistochastic forward-return pair with near-full diagonal trace is close to one permutation and its inverse
distinct_from:
  rectangular-escape: that permits larger target alphabets and reciprocal multiplicity loss; this theorem applies only after source and target have been closed to the same finite label space.
  common-self-map-law: that asks for one common classical mixture for all Leavitt arrows; this rounds one square forward-return pair once such a common coordinate space has been supplied.
---

Let `K,L` be `N by N` bistochastic matrices and put

```text
d_1(K,L)=(1/(2N)) sum_(i,j)|K_(ij)-L_(ij)|.           (BDR1)
```

If

```text
(1/N) Tr(LK) >= 1-eta,                               (BDR2)
```

then there is a permutation `pi in S_N` such that

```text
d_1(K,P_pi) <= 2 eta,
d_1(L,P_(pi^(-1))) <= 5 eta.                         (BDR3)
```

The constants are independent of `N`.

Indeed, bistochasticity gives `||K||_F,||L||_F<=sqrt(N)`.  Since
`Tr(LK)=<L^T,K>_F`, `(BDR2)` and Cauchy--Schwarz imply

```text
||K||_F^2 >= N(1-eta)^2.                             (BDR4)
```

Write `K=sum_sigma lambda_sigma P_sigma` by Birkhoff--von Neumann.  Some
`pi` has

```text
<K,P_pi>_F >= ||K||_F^2.                             (BDR5)
```

For bistochastic `K`,

```text
d_1(K,P_pi)=1-(1/N)<K,P_pi>_F <=2 eta.               (BDR6)
```

Finally, because every entry of `L` lies in `[0,1]`,

```text
|(1/N)Tr(L(K-P_pi))| <= 2 d_1(K,P_pi) <=4 eta.       (BDR7)
```

Thus `(1/N)Tr(LP_pi)>=1-5eta`, which is precisely the second estimate in
`(BDR3)` with the inverse orientation.

This removes near-bijection as an independent analytic gate after
same-sized closure.  It does not address rectangular transitions: a
forward map into a larger alphabet can have an exact return while shrinking
multiplicity, so square closure remains load-bearing.
