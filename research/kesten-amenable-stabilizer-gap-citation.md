---
rg: 2
id: kesten-amenable-stabilizer-gap-citation
kind: route
title: Induce Kesten's amenability criterion through an amenable subgroup
target: kesten-amenable-stabilizer-uniform-gap
requires: []
---

**Established by citation plus one standard induction step.**

Kesten's criterion (H. Kesten, *Symmetric random walks on groups*, Trans. AMS
92 (1959) 336--354; see also Pestov's survey, section on amenability): for a
finite symmetric generating set `S`, the Markov operator of the simple random
walk on `A` has norm `1` in `lambda_A` exactly when `A` is amenable, so
nonamenability gives `rho(A,S) < 1`.

Induction preserves weak containment, and `H` amenable gives
`1_H` weakly contained in `lambda_H`, so

```text
l^2(A/H) = Ind_H^A 1_H  weakly contained in  Ind_H^A lambda_H = lambda_A.
```

Hence the Markov operator `M = (1/|S|) sum_s pi(s)` of the quasi-regular
representation `pi` on `l^2(A/H)` satisfies `||M|| <= rho(A,S)`.  It is
self-adjoint because `S` is symmetric, so for real `f`

```text
sum_s || f - s f ||_2^2 = 2 |S| ( ||f||_2^2 - <M f, f> )
                       >= 2 |S| (1 - rho) ||f||_2^2,
```

which is `(KAG2)` with the constant `(KAG1)`.
