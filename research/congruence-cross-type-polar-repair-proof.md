---
rg: 2
id: congruence-cross-type-polar-repair-proof
kind: route
title: Average the cross-type unitary and truncate its polar part
target: congruence-cross-type-mixing-has-uniform-polar-repair
requires:
  - odd-congruence-iwahori-pairs-have-uniform-linear-repair
---

The cited odd-congruence result supplies a level- and
dimension-independent constant `kappa > 0` for the left-right action on
normalized Hilbert--Schmidt matrices.  For the representations `pi,sigma`
and unitary `U` in `(CCM1)--(CCM2)`, let

```text
K = Hom_Q(sigma,pi)
```

and let `Z` be the Hilbert--Schmidt orthogonal projection of `U` onto `K`.
Equivalently,

```text
Z = |Q|^(-1) sum_(g in Q) pi(g) U sigma(g)^*.
```

Thus `Z` is an exact intertwiner and a contraction.  The uniform gap gives

```text
delta := ||U-Z||_2^2 <= E(U)/kappa.                    (CPR1)
```

Write `H=|Z|`; then `H` commutes with `sigma(Q)`.  Put

```text
P  = 1_[1/2,1](H),
P' = range(ZP),
V  = polar(ZP).
```

Both projections reduce the relevant representations, have equal rank, and
`V=P'VP` is an exact partial intertwiner.  On an orthonormal eigenbasis of
`H` in `P^perp`, contraction by `Z` is at most `1/2`, whereas `U` is an
isometry.  Hence

```text
tr_d(1-P) <= 4 delta;
```

equal rank gives the same bound for `P'`.  The polar factor is a nearest
partial isometry to `ZP`, while `UP` is another partial isometry with initial
projection `P`.  Therefore

```text
||UP-V||_2
  <= ||UP-ZP||_2 + ||ZP-V||_2
  <= 2 ||U-Z||_2,
```

so `||UP-V||_2^2 <= 4 delta`.  The initial spaces of `UP-V` and
`U(1-P)` are orthogonal, and consequently

```text
||U-V||_2^2
 = ||UP-V||_2^2 + ||U(1-P)||_2^2
 <= 4 delta + tr_d(1-P)
 <= 8 E(U)/kappa.                                    (CPR2)
```

These are exactly `(CCM3)--(CCM4)`.  Decomposing `pi` and `sigma` into
irreducibles identifies the discarded supports with the unmatched
multiplicities; adjoining the complementary types crosswise extends `V` to
an exact unitary intertwiner and adds at most `4E(U)d/kappa` dimensions per
side.  This proves the asserted flexible-padding form as well.
