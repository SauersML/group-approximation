---
rg: 2
id: weyl-return-frame-rectangular-proof
kind: route
title: Expand the source commutant in the refined Weyl error basis
target: weyl-return-frame-is-exact-rectangular-escape
requires: []
---

Equip every matrix algebra with normalized Hilbert--Schmidt inner product.
The Weyl operators satisfy

```text
tr(W_a^*W_b)=delta_(a,b)
```

and form an orthonormal basis of `M_(p^r)`.  Therefore `(WRF1)` has the
orthogonal decomposition

```text
Ran(R_s)=directSum_a H_a,
H_a=I_(p^L) tensor W_a tensor M_m.                      (WRP1)
```

Let `P_a` be the orthogonal projection onto `H_a`.  Conditional expectation
from `Ran(R_s)` onto `Ran(R_t)` is normalized trace in the middle factor.
For `B in M_m`, direct substitution in `(WRF3)` gives

```text
X_a(I tensor W_b tensor B)
 =I tensor tr(W_a^*W_b)I tensor B
 =delta_(a,b)(I tensor I tensor B).                    (WRP2)
```

Thus `X_a` kills every `H_b` with `b!=a` and is an isometry from `H_a`
onto `Ran(R_t)`.  This proves

```text
X_a^*X_a=P_a,       X_aX_a^*=R_t.
```

Summing the mutually orthogonal `P_a` proves `(WRF4)--(WRF5)`.  For
`a!=b`, the two operators have orthogonal initial spaces, so their
Hilbert--Schmidt inner product is zero.  Each has squared norm
`tr_ad(R_t)=p^(-2(L+r))`; expanding the square proves `(WRF6)`, and `(WRF7)`
is immediate.

The construction uses only the refined Weyl factor and survives arbitrary
spectator multiplicity `m`, fixed tag amplification, and iteration in `r`.
It is exactly the concrete sharpness model left abstract in
`leavitt-target-return-channel-count-firewall`.
