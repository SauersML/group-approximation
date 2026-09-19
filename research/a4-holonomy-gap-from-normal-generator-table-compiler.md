---
rg: 2
id: a4-holonomy-gap-from-normal-generator-table-compiler
kind: route
title: Approximate A8 table trivialization turns the 19243 readout into chart-frame collapse
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-full-packet-normal-generator-table-compiler
  - finite-normal-generator-approximate-table-trivialization
  - atlas-a4-19243-parabolic-normal-closure
---

For the compiler output `u_n`, set

```text
eps_n = max_(x,y)||u_n(xy)-u_n(x)u_n(y)||_2,
delta_n = ||u_n(b)-1||_2.
```

The normalized-network assumptions and `(A4-TABLE-1)`--`(A4-TABLE-2)` give

```text
eps_n -> 0,
delta_n -> 0.
```

By `atlas-a4-19243-parabolic-normal-closure`, the same collision involution
`b` normally generates the full chart group `A8`.  Apply
`finite-normal-generator-approximate-table-trivialization` directly to `u_n`:

```text
max_(x in A8)||u_n(x)-1||_2 -> 0.
```

No exactification of `u_n` is used.  The decoder inequality `(A4-TABLE-3)` now
gives

```text
dist_2(U_n,lambda_(k_n)(A8)') -> 0.
```

As in the exact-representation route, choose a nearest commutant element
`Y_n`.  For each of the two fixed raw-S3 covariance generators `h_a,h_b`,

```text
||[U_n,lambda(h)]||_2 <= 2||U_n-Y_n||_2 -> 0.
```

Therefore `a_n^2+b_n^2->0`, which is stronger than the desired
`limsup < 1/128`.  This establishes `atlas-a4-holonomy-coherence-gap`.

The improvement over the exact-representation compiler is substantive: the
entire integer-multiplicity/representation-rounding layer disappears.  The
remaining open work is only to expose a bounded-error **finite A8 multiplication
table** in the four packet holonomies and identify the collision readout.
