---
rg: 2
id: finite-graph-product-amplifications-block-hs-collapse
kind: claim
title: Finite quotient amplifications give a zero-defect obstruction to graph-product HS abelianization
distinct_from:
  augmentation-boundary-expands-but-not-products: that constructs the exact infinite graph-product escape; this proves that, for residually finite actors, every missing commutator in that escape is witnessed by arbitrarily large finite-dimensional exact representations with maximal normalized-HS separation.
  finite-orbital-checksum-cannot-expose-sl3-coset-module: that is the algebraic finite-orbital obstruction for one coset action; this is the matricial amplification theorem for the regular actor graph and shows that spectral expansion of the checked edge graph cannot repair the obstruction.
  chordal-abelian-graph-products-hs-stable: that corrects approximate representations to exact representations of certain graph products; the exact representations here are already the obstruction and therefore cannot be removed by HS stability.
---

Let `A` be a residually finite group, let `D subset A` be finite, and let
`Graph_D(A)` be the left-invariant graph in which distinct `g,h` are joined
when

```text
g^(-1)h in D union D^(-1).
```

Write `K_D` for the graph product with one vertex group
`C_2=<c_g>` at each `g in A`, and put

```text
G_D=K_D rtimes A.                                      (FQA1)
```

If `r` is not in `{1} union D union D^(-1)`, then there are finite-dimensional
unitary representations `rho_n` of `G_D`, with dimensions tending to infinity,
such that every defining involution, edge-commutation, actor, and covariance
relation is exact while

```text
||rho_n([c_1,c_r])-I||_2=sqrt(2)                       (FQA2)
```

for every `n`.

In particular no modulus `omega(t)->0` can uniformly abelianize the lamp
kernel from the graph-product relations in normalized Hilbert--Schmidt norm.
This remains true when `A` has property `(T)` and `D` contains a Kazhdan
generating set, so that the corresponding finite quotient Cayley graphs form
an expander family.  Spectral expansion of the checked commutation graph does
not turn its missing edges into analytic consequences: the obstruction already
occurs at zero defect.

The only surviving positive construction must add a relation involving new
non-graph-product controller data whose finite quotients kill the missing
commutator.  Neither a bounded-degree Cayley boundary, all translates of
finitely many valid lamp words, nor a spectral/cosystolic inequality imposed
on the resulting edge graph can do so.
