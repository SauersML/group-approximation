---
rg: 2
id: gauge-doubling-gives-selector-flip-symmetries
kind: claim
title: Gauge doubling gives every BCS variable a constraint-preserving selector flip
distinct_from:
  fresh-selector-renewal-after-symplectic-chart-reset: that must transport a finite packet multiplicity current; this supplies the missing global symmetry and exact marked completeness model but not the reverse spin bridge.
---

Let `B` be a finite Boolean constraint system with involution variables `X_x`.
Construct `G(B)` by retaining the logical variables and, for every context
incidence `(c,x)`, adjoining two private share involutions

```text
A_(c,x), B_(c,x),          X_x=A_(c,x) B_(c,x).         (GDB1)
```

In context `c`, replace each Boolean bit `x` by the parity of its two local
shares. All shares occurring in one lifted context commute. Then:

1. `B` has a classical, finite-dimensional operator, tracial, or arbitrary
   operator solution if and only if `G(B)` has the corresponding solution.
2. The retained logical generators embed the BCS algebra of `B` into that of
   `G(B)`. The map `A_(c,x) -> X_x`, `B_(c,x) -> 1` is a left inverse; hence every nonzero
   logical signal remains nonzero after gauge doubling.
3. For every incidence `(c,x)`, the simultaneous sign flip

```text
theta_(c,x)(A_(c,x))=-A_(c,x),
theta_(c,x)(B_(c,x))=-B_(c,x)                            (GDB2)
```

   fixes every logical word `A_y B_y`, preserves every lifted constraint, and
   commutes with all other gauge flips. Thus one finite elementary abelian
   incidence-gauge group acts by BCS-algebra
   automorphisms and fixes the embedded original algebra pointwise.
4. Every exact marked representation can be made covariant for this entire
   gauge group without losing the mark: replace `pi` by

```text
direct_sum_(g in Gauge(B)) pi composed theta_g.          (GDB3)
```

   The regular permutation unitaries implement the flips.

On an exactly commuting context, the joint spectral distribution of the
shares pushes forward under `(a_x,b_x)->a_x+b_x` to the logical distribution.
Therefore forbidden mass is preserved exactly. For approximate involutions
and commutators, the product words in `(GDB1)` have defect bounded by a fixed
sum of the share defects, so a fixed BCS loses only a fixed normalized-HS
constant.

In central-sign group notation, `(GDB2)` is

```text
A_(c,x) -> J A_(c,x),  B_(c,x) -> J B_(c,x),            (GDB4)
```

and the invariant logical word is still `A_(c,x)B_(c,x)=X_x`. Hence a Weyl reset may
translate the nonzero selector direction `(1,1)` while leaving every original
BCS word and the native Fanizza signal unchanged.
