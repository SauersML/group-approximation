---
rg: 2
id: zero-dimensional-map-local-fd-proof
kind: route
title: Normalize a nearly unital order-zero outgoing map to a finite-dimensional homomorphism
target: zero-dimensional-unital-maps-are-locally-fd
requires: []
---

## Proof

Choose a zero-dimensional approximation

```text
A --alpha--> E --beta--> B
```

on `F union {1}`, where `E` is finite dimensional, `alpha` is cpc, `beta`
is cpc order zero, and `beta alpha` is sufficiently close to `phi`.  Put
`h=beta(1_E)`.  Since `0<=alpha(1)<=1_E`,

```text
0 <= beta(alpha(1)) <= h <= 1_B.
```

Closeness of `beta alpha(1)` to `phi(1)=1` therefore makes `h` as close to
`1` as desired.  In particular `h` is invertible.

The order-zero structure theorem writes

```text
beta(x)=pi(x)h=h pi(x),
```

where `pi:E->B**` is the supporting homomorphism.  Invertibility of `h`
puts the support at `1` and gives

```text
pi(x)=beta(x)h^(-1) in B.
```

Thus `pi` is a unital homomorphism into `B`, and `D=pi(E)` is a unital
finite-dimensional subalgebra.  Moreover

```text
||beta(x)-pi(x)|| <= ||h-1|| ||x||,
```

so `pi alpha(a)` approximates `phi(a)` uniformly on `F` after choosing the
original approximation sufficiently accurately.
