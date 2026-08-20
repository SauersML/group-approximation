---
rg: 2
id: iwahori-low-gap-cluster-atomization
kind: claim
title: Low-gap Iwahori cluster unitaries atomize into orthogonal type-pair intertwiners
---

Assume the componentwise stabilized unitaries supplied by
`iwahori-low-gap-cluster-integralization` for thresholds `a_n->0`.  Ask that,
after another `o(d_n)` stabilization and an `o(1)` normalized-HS perturbation,
each connected-component unitary split as an orthogonal direct sum

```text
W_(n,C) ~= directSum_k U_(n,k),
U_(n,k): V_(n,k) -> W_(n,k),
```

where for every `k` there is a **single edge** `(i,j)` of the low-gap graph
such that

```text
V_(n,k) <= Q_(n,j),
W_(n,k) <= P_(n,i),
dim V_(n,k)=dim W_(n,k),
lambda_(n,i,j)<a_n,
```

and the aggregate Iwahori intertwining defect of the direct sum still tends to
zero.

This is now the precise noncommutative atomization gate.  Scalar mass flow and
whole-cluster unitarization are not the issue: the problem is whether a unitary
spread across several nearly compatible irreducible types can be made
approximately monomial with respect to the two isotypic decompositions.

## Attempts

1. **Polar-decompose every matrix block.**  Initial spaces from different
   blocks in one column and final spaces from different blocks in one row need
   not be orthogonal, so the polar parts need not assemble to a unitary.
2. **Use only the scalar overlap plan.**  A Fourier unitary between two
   rank-one decompositions has a perfectly bistochastic overlap matrix but is
   a fixed normalized-HS distance from every monomial unitary.  Thus no theorem
   of this form is true without the representation-theoretic low-gap input.
3. **Whole-cluster polar rounding.**  This is established by
   `iwahori-low-gap-cluster-integralization`; it proves that physical-rank
   imbalance and cross-cluster leakage cost only `o(d_n)`.  What remains is
   entirely *inside* a low-gap connected component.

The intended extra input is the opposite modular-extension geometry: the
index-three theorem gives bounded restriction/induction branching, while
`iwahori-nielsen-extension-transversality` is designed to prevent long chains
of distinct low-gap types from behaving like the Fourier counterexample.