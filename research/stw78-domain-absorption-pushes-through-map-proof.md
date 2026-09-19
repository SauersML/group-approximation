---
rg: 2
id: stw78-domain-absorption-pushes-through-map-proof
kind: route
title: Push the central O-infinity copy from the domain into the map commutant
target: stw78-traceless-domain-branch-is-automatic
requires: []
---

Because `A` is exact, its normalized quasitraces are traces.  Rordam's
traceless `Z`-stability theorem therefore gives

```text
A ~= A tensor_min O_infinity.
```

Equivalently, strong self-absorption supplies a unital embedding

```text
eta:O_infinity -> A_infinity cap A'.
```

Apply `phi` coordinatewise to obtain a unital star homomorphism

```text
phi_infinity:A_infinity->B_infinity.
```

For `d in O_infinity` and `a in A`, the element
`phi_infinity(eta(d))` commutes with `phi(a)`.  Hence the composite is a
unital homomorphism

```text
O_infinity -> B_infinity cap phi(A)'.
```

It is injective because `O_infinity` is simple and the composite is unital.
This is exactly `O_infinity`-stability of `phi`.

The two domain branches are exhaustive.  If `A` has a normalized trace,
simplicity makes it faithful and therefore makes `A` stably finite.  If it
does not, the preceding argument applies.  Thus the general LXXVIII problem
is equivalent to its traceful stably finite restriction.

