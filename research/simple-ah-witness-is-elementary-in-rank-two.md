---
rg: 2
id: simple-ah-witness-is-elementary-in-rank-two
kind: claim
title: The AH unitary witness becomes elementary after one amplification
distinct_from:
  stw59-simple-ah-non-k1-injective: that records that diag(v,1) is null-homotopic in U(M_2(A)), a topological statement; this gives the algebraic factorization into elementary matrices, which is strictly stronger and yields vanishing in algebraic K_1.
  topological-k1-cannot-detect-integral-whitehead: that is the methodological no-go about a vanishing corona K_1 detecting nothing about algebraic K_1; this is a positive algebraic factorization in one concrete algebra.
  stw59-exact-factorial-unitary-component-groups: that computes the whole unitary component group; this concerns what happens to one class after amplification, in the algebraic rather than the homotopical category.
artifacts:
  - research/artifacts/ah-k1-mf-bridge-2026-09-07.md
---

Let `A` and `v in U(A)` be as in `stw59-simple-ah-non-k1-injective`, with
`v` the image of a generator of `pi_4(U(2))`.  Choosing the generator as a
map `u : S^4 -> SU(2)`,

```text
diag(v, 1_A) in E_2(A),
```

so the class of `v` in algebraic `K_1(A) = GL_infinity(A)/E_infinity(A)`
is zero.

This is stronger than the recorded null-homotopy of `diag(v,1_A)` in
`U(M_2(A))`: the factorization is by elementary matrices over the ring `A`.
