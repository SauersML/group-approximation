---
rg: 2
id: three-way-cell-semigroups-have-conductor-but-unbounded-charge
kind: claim
title: Fixed three-way cell supports have conductors, but moving supports carry unbounded lattice charge
distinct_from:
  bs14-two-exit-typed-transport-is-not-saturated: that exhibits one determinant-two hole; this separates all fixed-support saturation holes from lattice-charge holes and constructs charges of every order.
  bs14-native-cell-padding-preserves-lattice-charge: that proves a wrong-lattice margin cannot be repaired on the same support; this proves the converse conductor statement in the correct lattice and shows that the charge exponent is not uniformly bounded over finite supports.
  fixed-level-bs14-compatible-basin: that isolates an analytic fixed-level stability radius; this closes only the affine-semigroup arithmetic at one fixed cell support and does not supply the analytic basin or a moving-level bound.
---

Let `E` be a finite set of admissible joint cells in a three-way
source/first-exit/second-exit table, and let `A_E` be its vertex--cell
incidence matrix.  Put

```text
S_E=A_E N^E,                 L_E=A_E Z^E,
C_E=A_E R_+^E,               Sbar_E=C_E intersect L_E.       (TSC1)
```

There is a fixed conductor packet `c_E in S_E` such that

```text
c_E+Sbar_E subset S_E.                                      (TSC2)
```

Consequently every fractional cell table whose integral margins lie in the
correct lattice `L_E` becomes an integral table after adding one fixed exact
packet.  For a fixed support, nonnormality of the positive semigroup is
therefore harmless for qualitative flexible normalized-HS repair: the
absolute padding in `(TSC2)` is independent of the multiplicities.

The lattice condition is load-bearing and has no support-independent finite
exponent.  For every `n>=2`, take source and first-exit labels in `Z/n` and
two second-exit labels `0,1`.  Allow the `2n` cells

```text
c_i=(i,i,0),                   d_i=(i,i+1,1),
i in Z/n.                                                   (TSC3)
```

For every `1<=m<n`, the integral margin vector

```text
s_i=1,       e_i=1       for all i,
k_0=m,       k_1=n-m                                      (TSC4)
```

lies in `C_(E_n)` but not in `L_(E_n)`.  Its lattice class for `m=1` has
exact order `n`.  Thus moving three-way supports admit fractional tables
whose same-support additive-padding obstruction has arbitrarily large
order, even though multiplying the whole table by `n` makes it integral.

Applied to the BS14 two-cubic boundary problem, this gives a sharp algebraic
division of labor.  At an authenticated fixed native support, the conductor
removes every positive-semigroup hole after the lattice charge is known to
vanish.  Across moving congruence levels, neither fractional transport nor a
uniform saturation exponent controls the charge: a proof must show that the
native operator Gram data land in the correct lattice, or must construct
energy-paid support-changing cells.  The abstract examples `(TSC3)` are a
firewall, not a claim that the BS14 native support realizes them.
