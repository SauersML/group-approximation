---
rg: 2
id: three-anchored-root-cells-proof
kind: route
title: Factor q through three prefixes on the four-root overlap carrier
target: marked-root-star-carries-three-anchored-cells
requires:
  - seventeen-root-star-has-marked-triple-overlap
---

The `k=3` instance of `(SRS2)` gives `(ARC1)`.  Prefix cancellation gives

```text
t_(0^m)s_(0^m)=1,              t_1s_1=1,
```

and hence every identity in `(ARC4)`.

For the three displayed root pairs, the Steinberg product rule gives

```text
[x_(i,k)(a_m),x_(k,2)(b_m)]=x_(i,2)(a_mb_m)=x_(i,2)(q)
```

with `(i,k)=(4,7),(5,8),(6,9)`.  All cross commutators vanish because the
six off-diagonal root positions have no composable cross pair.  Each central
root `x_42(q),x_52(q),x_62(q)` commutes with all six generators, as does the
marked root `x_13(q)`, so `F` reduces the entire finite packet.

On `FH` the three central roots act as `-1`.  Therefore each pair
`A_m,B_m` anticommutes, while different pairs commute.  The elementary
three-pair extraspecial representation calculation gives a tensor product of
three Pauli factors and an arbitrary multiplicity space, proving `(ARC3)`.
