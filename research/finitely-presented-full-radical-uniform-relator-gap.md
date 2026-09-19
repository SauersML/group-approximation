---
rg: 2
id: finitely-presented-full-radical-uniform-relator-gap
kind: claim
title: A finite presentation has full MF radical exactly when its relators have a uniform trivial-sector gap
artifacts:
  - research/finitely-presented-full-radical-uniform-relator-gap-proof.md
---

Let

```text
G = <s_1,...,s_k | r_1,...,r_m>
```

be a finitely presented group.  Then `Rad_MF(G)=G` if and only if, for every
`epsilon>0`, there is `delta>0` such that every tuple
`U=(U_1,...,U_k)` of same-size unitary matrices satisfying

```text
max_j ||r_j(U)-1|| < delta
```

also satisfies

```text
max_i ||U_i-1|| < epsilon.                       (R1)
```

Equivalently, the presentation soundness profile

```text
gap_G(epsilon)
 = inf max_j ||r_j(U)-1||,
```

where the infimum ranges over all matrix sizes and all tuples with
`max_i||U_i-1|| >= epsilon`, is strictly positive for every `epsilon>0`.

The finitely presented Hilbert-hotel cover has this property.  It is a fixed
finite system of unitary equations whose approximate matrix solutions have
no nontrivial sector in any dimension.
