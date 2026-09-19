---
rg: 2
id: odd-maslov-uniform-homogeneous-folner-gap-proof
kind: route
title: Direct-sum the coefficient GNS representations and invoke the odd-fibre Folner fence
target: odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap
requires:
  - deligne-fixed-projective-representation-folner-compression-no-go
  - odd-maslov-twisted-fibres-have-no-amenable-trace
---

Suppose `(OUF2)` had no dimension-uniform constant.  Choose sizes `n_k` and
normalized `delta`-positive-definite functions `C^(k)` whose displayed
energies tend to zero.  Let

```text
C_g^(k)=V_k^* pi_k(g)V_k                              (OUP1)
```

be their projective GNS compressions, where `pi_k` is an exact
`delta`-projective unitary representation, `V_k:C^(n_k)->H_k` is an
isometry, and `P_k=V_kV_k^*`.

For every generator `s`, direct expansion gives the exact boundary identity

```text
||[P_k,pi_k(s)]||_HS^2
 =Tr(I-C_s^(k)* C_s^(k))+Tr(I-C_s^(k) C_s^(k)*).       (OUP2)
```

Indeed the two terms are respectively the squared Hilbert--Schmidt norms of
`(I-P_k)pi_k(s)P_k` and `P_k pi_k(s)(I-P_k)`.

Now form the single exact projective representation

```text
pi=direct_sum_k pi_k                                    (OUP3)
```

and regard `P_k` as a finite-rank projection in its `k`-th summand.  Since
`rank(P_k)=n_k`, equations `(OUF2)` and `(OUP2)` would give

```text
||[P_k,pi(s)]||_HS/sqrt(rank P_k) ->0                  (OUP4)
```

for every `s in S`.  This is exactly the forbidden projective Folner
compression sequence of
`deligne-fixed-projective-representation-folner-compression-no-go`.
Therefore the infimum in `(OUF2)`, taken simultaneously over every `n` and
every coefficient function, is strictly positive.

Equivalently, one may apply the normalized compression states from the
Folner no-go proof to `(OUP3)`: a weak-star cluster point would pull back to
an amenable trace on the odd twisted fibre, contradicting
`odd-maslov-twisted-fibres-have-no-amenable-trace`.  The direct-sum argument
shows that no fixed-representation hypothesis is lost when the coefficient
GNS model varies with `k`.
