---
rg: 2
id: gauge-doubling-gives-selector-flip-symmetries
kind: claim
title: Gauge doubling gives every BCS variable a constraint-preserving selector flip
distinct_from:
  fresh-selector-renewal-after-symplectic-chart-reset: that must transport a finite packet multiplicity current; this supplies the missing global symmetry and exact marked completeness model but not the reverse spin bridge.
---

Let `B` be a finite Boolean constraint system with involution variables `X_x`.
Construct `G(B)` by replacing every variable with two share involutions

```text
A_x, B_x,                  X_x^log=A_x B_x,             (GDB1)
```

and, in every context, replacing each Boolean bit `x` by the parity of its two
shares. All shares occurring in one lifted context commute. Then:

1. `B` has a classical, finite-dimensional operator, tracial, or arbitrary
   operator solution if and only if `G(B)` has the corresponding solution.
2. The map `X_x -> A_x B_x` embeds the BCS algebra of `B` into that of `G(B)`.
   It has the left inverse `A_x -> X_x`, `B_x -> 1`; hence every nonzero
   logical signal remains nonzero after gauge doubling.
3. For every `x`, the simultaneous sign flip

```text
theta_x(A_x)=-A_x,       theta_x(B_x)=-B_x              (GDB2)
```

   fixes every logical word `A_y B_y`, preserves every lifted constraint, and
   commutes with all other gauge flips. Thus `F_2^X` acts by BCS-algebra
   automorphisms and fixes the embedded original algebra pointwise.
4. Every exact marked representation can be made covariant for this entire
   gauge group without losing the mark: replace `pi` by

```text
direct_sum_(g in F_2^X) pi composed theta_g.             (GDB3)
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
A_x -> J A_x,          B_x -> J B_x,                    (GDB4)
```

and the invariant logical word is still `A_x B_x`. Hence a Weyl reset may
translate the nonzero selector direction `(1,1)` while leaving every original
BCS word and the native Fanizza signal unchanged.
