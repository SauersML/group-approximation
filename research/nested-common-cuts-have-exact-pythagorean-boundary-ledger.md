---
rg: 2
id: nested-common-cuts-have-exact-pythagorean-boundary-ledger
kind: claim
title: Nested common cuts charge every off-diagonal block exactly once
distinct_from:
  common-cut-contraction-sign-has-complete-balanced-energy-ledger: that treats one cut and the eventual sign repair; this proves an exact cardinality-free identity for an arbitrary nested cut tree before the terminal sign
  sequential-pinchings-have-sharp-linear-disturbance-loss: that pinches by different coordinate spectral projections and can repeatedly disturb one coordinate; this uses one common nested physical partition and orthogonality of its block pairs
---

Let `Q_1,...,Q_L` be reflections in a finite tracial matrix algebra.  Let a
finite rooted binary tree of projections start at `e_root=1`, and let every
internal node `v` have orthogonal children `e_(v,0),e_(v,1)` with

```text
e_(v,0)+e_(v,1)=e_v.
```

At node `v`, measure the boundary against the tuple already compressed by
its ancestors:

```text
b_(v,i)^2
 =||[e_(v,0),e_v Q_i e_v]||_2^2
 =||e_(v,0)Q_i e_(v,1)+e_(v,1)Q_i e_(v,0)||_2^2.       (NCL1)
```

If `(f_a)` are the leaf projections and

```text
Phi_F(T)=sum_a f_a T f_a,
```

then, for every `i`,

```text
sum_(v internal)b_(v,i)^2
 =||Q_i-Phi_F(Q_i)||_2^2.                               (NCL2)
```

Consequently

```text
sum_v (1/L)sum_i b_(v,i)^2
 =(1/L)sum_i||Q_i-Phi_F(Q_i)||_2^2 <=1.                 (NCL3)
```

Thus nested common cutting has no hidden depth or entropy multiplicity:
each ordered off-diagonal leaf block is paid exactly at the lowest common
ancestor of its two leaves.  More importantly, the desired `o(1)` total
boundary is equivalent to the final common pinching satisfying

```text
(1/L)sum_i||Q_i-Phi_F(Q_i)||_2^2=o(1).                  (NCL4)
```

The identity requires that intermediate nodes retain the compressed
contractions `e_v Q_i e_v`.  Signing after every cut changes later operators
and destroys the orthogonality ledger.  The safe schedule is to defer polar
sign repair until the terminal partition and then apply
`common-cut-contraction-sign-has-complete-balanced-energy-ledger` once.

## Attempts

Charging a cut to the trace of its smaller child introduces a logarithmic
entropy loss and is unnecessary.  Equation `(NCL2)` is the exact replacement.
It does not prove `(NCL4)`: a final fine pinching can move an order-one part of
every generator even though no matrix coefficient was charged twice.
