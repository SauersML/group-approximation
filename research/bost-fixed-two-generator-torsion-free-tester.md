---
rg: 2
id: bost-fixed-two-generator-torsion-free-tester
kind: claim
title: One two-generator nonsofic non-MF group tests the torsion-free Bost conjecture with coefficients
distinct_from:
  full-farrell-jones-fixed-fp-torsion-free-tester: that concerns algebraic K- and L-theory over the virtually-cyclic family with additive-category coefficients and finite wreath products; this concerns topological K-theory of the L1 crossed product over the finite-subgroup family.
  connective-loday-assembly-fixed-fp-torsion-free-tester: that concerns connective integral algebraic K-theory over the trivial family; this concerns all degrees of the analytic Bost assembly with separable C-star-algebra coefficients.
  two-generator-fp-torsion-free-master-tester: that supplies the abstract universal host; this verifies the coefficient-sensitive literature hypotheses needed for the Bost instance.
---

Let `Bost(G)` mean the Bost conjecture with arbitrary separable
C-star-algebra coefficients: for every separable `G`-C-star-algebra `A`
and every `n in Z`, the L1 assembly map

```text
H_n^G(E_FIN(G); K^top_(A,L1))
  ->
K_n(A crossed_product_L1 G)
```

is an isomorphism.

There exists one two-generator finitely presented torsion-free group `E`,
simultaneously nonsofic and non-MF, such that

```text
Bost(E)
  <=>
Bost(G) for every torsion-free discrete group G.
```

The group `E` may be chosen as the witness in
[[two-generator-fp-torsion-free-master-tester]].

This is an exact reduction, not a proof of the Bost conjecture. It makes no
corresponding assertion for the reduced Baum--Connes conjecture: reduced
crossed products do not have the arbitrary-homomorphism colimit permanence
used here, and the distinction is essential.

**ESTABLISHED 2026-08-30** by
[[bost-fixed-two-generator-torsion-free-tester-proof]].
