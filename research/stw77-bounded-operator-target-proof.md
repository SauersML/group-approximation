---
rg: 2
id: stw77-bounded-operator-target-proof
kind: route
title: Use Voiculescu absorption to turn two representation copies into central isometries
target: stw77-bounded-operator-target-case
requires: []
---

## Proof

Put `C=phi(A)` and view the inclusion `iota:C->B(H)` as a faithful
nondegenerate representation.  It is essential.  Indeed, if
`0!=x in C intersect K(H)`, then `x^*x` is a nonzero positive compact in
`C`.  A nonzero spectral value of `x^*x` is isolated from zero after passing
to a suitable upper spectral interval, producing a nonzero finite-rank
spectral projection `p in C`.  Such a projection is not properly infinite in
`B(H)`, contrary to the hypothesis.

Voiculescu's noncommutative Weyl--von Neumann absorption theorem, applied to
the faithful essential representation `iota`, supplies unitaries

```text
U_n:H direct_sum H -> H
```

such that

```text
||U_n(iota(c) direct_sum iota(c))U_n^*-iota(c)|| -> 0  (c in C).
```

Let `j_1,j_2:H->H direct_sum H` be the coordinate isometries and put

```text
s_(r,n)=U_n j_r,                         r=1,2.
```

For every `n` these are exact isometries with orthogonal ranges:

```text
s_(r,n)^*s_(t,n)=delta_(r,t)1.
```

Moreover, multiplying the absorption estimate on the right by `U_n j_r`
gives

```text
||s_(r,n)iota(c)-iota(c)s_(r,n)|| -> 0   (c in C).
```

Thus the finite-set defects in
`oinfty-map-stability-is-central-isometry-splitting` vanish.  That criterion
proves O-infinity-stability.

The only imported result is Voiculescu's absorption theorem; the extraction
of the two central isometries is explicit above.
