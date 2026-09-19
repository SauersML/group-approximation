---
rg: 2
id: split-cu-tensor-purity-proof
kind: route
title: Almost unperforation and divisibility pass to a Cu-retract
target: split-cu-tensor-map-implies-pure-product
requires: []
---

Write

```text
S=Cu(A) tensor_Cu Cu(B),       T=Cu(A tensor_min B),
theta:S -> T,                  sigma:T -> S,
theta sigma=id_T.
```

First, `S` is pure.  Indeed, purity of `A` and `B` is equivalent to absorption
of the Cu-semiring `Cu(Z)`, and associativity gives

```text
S tensor_Cu Cu(Z)
  = Cu(A) tensor_Cu (Cu(B) tensor_Cu Cu(Z))
  = Cu(A) tensor_Cu Cu(B)
  = S.
```

Here is also a direct verification that the retract `T` inherits the two
order properties.  If

```text
(n+1)x <= n y
```

in `T`, applying `sigma`, almost unperforation of `S`, and then `theta` gives

```text
sigma(x)<=sigma(y),       hence       x<=y.
```

For almost divisibility, let `x' << x` in `T` and `n>=1`.  A Cu-morphism
preserves the way-below relation, so `sigma(x') << sigma(x)`.  Choose `z in S`
with

```text
n z <= sigma(x),          sigma(x') <= (n+1)z.
```

Applying `theta` gives

```text
n theta(z) <= x,          x' <= (n+1)theta(z).
```

Thus `T` is almost unperforated and almost divisible, which is precisely
pureness of `A tensor_min B`.
