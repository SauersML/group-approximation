---
rg: 2
id: hyperlinear-radical-presentation-compactness
kind: claim
title: Hyperlinear-radical membership is equivalent to non-effective finite-window HS collapse
distinct_from:
  hyperlinear-elementwise-visibility: that characterizes visibility by the existence of one homomorphism to one hyperlinear target; this gives the uniform finite-relator compactness form for a presented group.
  effective-transport-modulus: that asks for computable quantitative constants; the finite window and defect threshold here exist by ultraproduct compactness and need not be computable.
  group-algebra-mark-reverse-kleene-collapse: that consumes an asymptotic collapse theorem in a finite-presentation diagonal; this proves the equivalence between such collapse and hyperlinear-radical membership, including recursively enumerable presentations.
---

Let

```text
Gamma = <S | r_1,r_2,...>
```

have a finite generating set and a finite or recursively enumerable relator
list, and let `w in F(S)`.  The following are equivalent:

1. every homomorphism from `Gamma` to a tracial matrix ultraproduct kills
   `w`, equivalently `w` belongs to the hyperlinear radical of `Gamma`;
2. for every `epsilon>0` there are a finite relator window
   `r_1,...,r_N` and `delta>0` such that every finite-dimensional unitary
   tuple `U` satisfying

   ```text
   max_(j<=N) ||r_j(U)-I||_2 < delta
   ```

   also satisfies `||w(U)-I||_2<epsilon`.

For a finite presentation one may always take the whole relator list.  Neither
`N` nor `delta` is asserted computable.
