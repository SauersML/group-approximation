---
rg: 2
id: stw95-inner-cofinal-cu-image-gives-almost-divisibility-proof
kind: route
title: Divide a lifted way-below pair in the pure abstract Cu tensor product
target: stw95-inner-cofinal-cu-image-gives-almost-divisibility
requires: []
---

The pure semigroups `Cu(A)` and `Cu(B)` absorb `Cu(𝒵)`.  Associativity
shows that `S` absorbs `Cu(𝒵)` and is therefore almost divisible.  Fix
`n>=1` and `x'<<x` in `T`, and choose `a'<<a` as in the hypothesis.  There is
`y∈S` with

```text
n y <= a,     a' <= (n+1)y.
```

Applying `theta` gives

```text
n theta(y) <= theta(a) <= x,
x' <= theta(a') <= (n+1)theta(y).
```

This is exactly almost divisibility of `T`.  Neither an inverse to `theta` nor
order reflection was used.
