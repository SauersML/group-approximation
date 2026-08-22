---
rg: 2
id: random-iwahori-nielsen-matching-entropy-proof
kind: route
title: Union-bound the Hamming balls around all relabellings of a random Iwahori action
target: unconditioned-random-iwahori-actions-are-far-from-nielsen-matching
requires: []
---

Write `I_n` for the fixed-point-free involutions in `Sym(n)`.  Nielsen
precomposition is the bijection

```text
Phi:Sym(n) x I_n -> Sym(n) x I_n,
Phi(U,E)=(U^(-1)E,U^(-1)EU).                          (RIN1)
```

It is a bijection because `alpha^2=id`; the second coordinate remains in
`I_n` by conjugacy.  Hence `Phi` preserves the uniform measure on the
Cartesian product.  In particular the Nielsen-twisted target pair is again
an independent uniform permutation and fixed-point-free involution.

For any fixed permutation `P`, its Hamming ball of radius `epsilon n` has
size at most

```text
sum_(k<=epsilon n) binom(n,k) k!
 <= exp(epsilon n log n+O(n)).                        (RIN2)
```

The same crude bound holds for the intersection of such a ball with
`I_n`.  Stirling gives

```text
|Sym(n)|=exp(n log n+O(n)),
|I_n|=exp((n/2)log n+O(n)).                           (RIN3)
```

Condition on the source pair and fix one relabelling `S`.  By `(RIN1)` the
probability that both target generators lie in the required Hamming balls
is at most

```text
exp(-(3/2-2epsilon)n log n+O(n)).                     (RIN4)
```

There are `n!=exp(n log n+O(n))` choices of `S`.  The union bound is

```text
exp(-(1/2-2epsilon)n log n+O(n)),                     (RIN5)
```

which tends to zero for every fixed `epsilon<1/4`.

No modular extension condition was used.  Indeed, restrictions of
`C_2*C_3` dessins occupy a highly nongeneric subset of
`Hom(Z*C_2,Sym(n))`; conditioning on that rare locus can destroy the
independence in `(RIN4)`.  The theorem therefore eliminates generic random
edge matching, not correlated random modular dessins.

