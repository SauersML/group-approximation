---
rg: 2
id: dyadic-stable-heisenberg-sign-proof
kind: route
title: Compute the power and root-commutator invariants in the central pushout
target: dyadic-invariant-cocycle-has-a-stable-heisenberg-sign
requires:
  - fixed-clifford-projective-dyadic-tower
---

Invariance of `chi_a` makes `ker(chi_a)` normal in `G_a`, and the residual
copy `L_a/ker(chi_a)=<z>` is central in `E_a`.  Let `U=u(1)`.  Its image in
`G_(a-1)` has order `2^(a-1)`, while in `E_a`

```text
U^(2^(a-1))
 = class(1+2^(a-1)E_12)
 = z,                                                               (DHP1)
```

because `ell_0(0,1,0)=1`.  Every other lift is `z^epsilon U`; since
`2^(a-1)` is even, it has the same power.  No lift has the order required
by a splitting, proving that `(DHS1)` is nonsplit.

Now take `t=2^r`, `q=2^s` with `r+s=a-1`.  Direct multiplication gives,
modulo `2^a`,

```text
[1+tE_12,1+qE_21]
 = 1+tq(E_11-E_22),                                      (DHP2)
```

because the omitted terms are divisible by `t^2q` or `tq^2`, whose
2-adic valuations are at least `a`.  The two elements therefore commute
modulo `2^(a-1)`.  Their commutator in the kernel at level `a` has
last-layer coordinate

```text
X(1,0,0),
```

and `ell_0(1,0,0)=1`; its class in `E_a` is exactly `z`.  This proves
`(DHS3)`.  In a linearization of an `omega_a`-projective representation,
`z` acts by `-I`, hence the two operators anticommute.  Taking determinants
shows `(-1)^d=1`, so their dimension `d` is even.

The abstract Nielsen map on the Iwahori root parameters is

```text
u(t) -> u(2t),             l(q) -> l(q/2).                (DHP3)
```

On the integral overlap this changes `(r,s)` to `(r+1,s-1)` and preserves
`r+s=a-1`.  Formula `(DHP2)` therefore evaluates to the same last-layer
diagonal class and the same central sign.  Since the central group has
order two, dualizing or inverting the multiplier also preserves the sign.
Finally, even multiplicity is closed under arbitrary direct sums (and can
always be enforced by doubling), so this calculation supplies no positive
normalized-rank mismatch between the two shifted categories.
