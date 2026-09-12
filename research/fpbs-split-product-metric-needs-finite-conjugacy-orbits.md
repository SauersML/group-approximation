---
rg: 2
id: fpbs-split-product-metric-needs-finite-conjugacy-orbits
kind: claim
title: The product-coordinate metric on a semidirect product is left-invariant and proper only when conjugation orbits are finite
distinct_from:
  fpbs-quotient-split-not-bernoulli-contained: that shows no action with a nontrivial N-invariant factor is weakly contained in the Bernoulli shift, killing the weak-containment upgrade of Theorem A; this shows the product-coordinate metric behind Khezeli's horoball process is not left-invariant on N semidirect H once conjugation has an infinite orbit, killing the literal transfer of the product proof.
---

**ESTABLISHED.** Let `Gamma = N semidirect H` with `N` and `H` countable, and
write each element uniquely as `n h`. Let `l_N` and `l_H` be proper length
functions, meaning every ball is finite, and let `c > 0`. Put

```text
rho(n h, n' h') = l_N(n^-1 n') + l_H(h^-1 h') / c.
```

If `rho` is invariant under left multiplication by `Gamma`, then every
`H`-conjugacy orbit in `N` is finite. The proof is
`fpbs-split-product-metric-needs-finite-conjugacy-orbits-proof`.

**Burnside instance.** Take `m >= 3` and a sufficiently large odd `n`, with
`B(m,n) = <<x_1>> semidirect <x_2,...,x_m>` as in
`fpbs-burnside-normal-closure-split`. Here the `H`-orbit of `x_1` is infinite:
* `C_H(x_1)` lies in the centralizer of `x_1`, which is cyclic by
  `fpbs-burnside-embedding-input`, and so finite in a torsion group;
* `H = B(m-1,n)` is infinite.

So no metric of this product form exists on that split.

**What it rules out.** Khezeli, arXiv:2509.08325, proves fixed price one for
`G x G'` from weak limits of factors of i.i.d. built on the weighted product
metric `d + d'/c`. Its horoballs are sandwiched between product horoballs with
centres in `∂G x ∂G'`, and they have infinite sections in both coordinates.
Commutation of the factors is what makes that metric left-invariant.

For the split form of `fpbs-normal-subgroup-bounded-cost-fixed-price-one`, and
so for the Burnside route `fpbs-burnside-upper-cost-one-via-normal-closure`, the
literal transfer of the metric fails. An adaptation needs a non-product
left-invariant metric whose horoballs still have infinite `N`- and `H`-sections.
None is constructed here. This kills the literal transfer, not the horoball
method.
