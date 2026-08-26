---
rg: 2
id: endpoint-whitehead-placement-trichotomy-proof
kind: route
title: Enumerate endpoint incidences and compute the unique fine-flag half-cut
target: endpoint-whitehead-placements-have-a-three-way-hecke-flag-trichotomy
requires:
  - endpoint-detector-cell-retains-coboundary-gauge
  - center-chain-hecke-polar-supports-are-nested-pauli-flags
  - fixed-center-chain-hecke-occurrence-is-regularly-impossible
---

The partial Whitehead coefficients are

```text
c_m=s_(0^(m+1))t_(0^m),       d_m=s_(0^m)t_(0^(m+1)).
```

Since `q=s_1t_1` is orthogonal to every zero-prefix support, conjugation by
any legal endpoint Whitehead preserves each simple `q`-root in `H` and its
sign.  A flag root can move only if the endpoint word meets its terminal
coordinate.  The two coarse roots `v,w` terminate at `7`, while the extra
fine root `s` terminates at `8`.  This proves the three cases in `(EPT1)--
(EPT3)`; the faithful-prefix enumeration checks all coincidences, both
orientations and both depths.

For the prioritized edge `(8,2;2)`, prefix cancellation gives

```text
a_2d_2=a_3.
```

Direct Steinberg conjugation therefore gives

```text
x_68(a_2) |-> x_62(a_3),       x_58(a_2) |-> x_52(a_3),
```

while all generators of `K_1` and `A_1` are fixed.  The exact generated
group audit gives the four orders in `(EPT5)` and equality of the two
characters on the intersection.  Since the join has the product order

```text
512*512/256=1024,
```

the subgroup product is the join and the two character projections commute.
The standard finite-character multiplication formula then yields

```text
e_(K_2,lambda)e_(K_2',lambda')
 =e_(<K_2,K_2'>,lambda_join)=p_*.
```

Conjugation sends `p_2` to the second factor.  Compressing the involution
`W` by `p_2` proves `(EPT6)`.  Finally `W` interchanges the two factors and
hence normalizes their join and reduces `p_*`.  The cut is therefore fixed
and regular, so the established regular-trace firewall excludes its
promotion to the native affine rows.  This proves the claim.
