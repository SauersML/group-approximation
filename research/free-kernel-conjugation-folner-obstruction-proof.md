---
rg: 2
id: free-kernel-conjugation-folner-obstruction-proof
kind: route
title: Extend a kernel conjugation mean to the free group and compute weighted-energy covariance
target: free-presentation-kernel-has-no-conjugation-folner-exhaustion
requires: []
---

Suppose first that there were a net of finitely supported probability
measures `mu_i` on `K\{1}` with

```text
||s_*mu_i-mu_i||_1 -> 0                                (CKP1)
```

for every `s in F`. Any weak-star cluster point in the dual of
`ell^infinity(K\{1})` would be an `F`-conjugation-invariant mean on
`K\{1}`. Because `K` is normal, this mean extends by

```text
m_tilde(phi)=m(phi|_(K\{1}))                           (CKP2)
```

to an `F`-conjugation-invariant mean on `F\{1}`. That would make `F` inner
amenable. A nonabelian free group is not inner amenable, a contradiction.

The Reiter characterization of amenable actions now gives a finite
`S<=F` and `eta>0` for which `(CKE1)` holds. Equivalently, if no such finite
pair existed, the directed family over finite subsets of `F` and positive
errors would give a net satisfying `(CKP1)`.

For the operator calculation, expand

```text
D_k=2-Pi(k)-Pi(k)^*.
```

Exact multiplicativity and normality give

```text
Pi(s)D_kPi(s)^*=D_(sks^(-1)),
```

which proves `(CKE3)` after reindexing. Since `||D_k||_op<=4`, the triangle
inequality proves `(CKE4)`.

Finally let `Q=1-P`. On the source of `P`, `A_mu<=a`, while on the range of
`Q`, `A_mu>=b`. The usual Sylvester/off-diagonal estimate therefore gives

```text
(b-a)||QPi(s)P||_op
 <=||Q(A_mu Pi(s)-Pi(s)A_mu)P||_op,
```

and hence `(CKE5)`. This is precisely the spectral-cut mechanism suggested
for the presentation-double kernel energy. Its coefficientwise version needs
the nonexistent probabilities `(CKP1)`; any remaining route must exploit
relations among the concrete matrices `D_k`, rather than normality of `K`
alone.
