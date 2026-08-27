---
rg: 2
id: atlas-ef-dual-prefix-tower-proof
kind: route
title: Iterate the E/F incidence returns into the binary prefix Heisenberg packet
target: atlas-ef-dual-rows-create-the-prefix-depth-tower
requires:
  - atlas-ef-target-rows-shrink-but-do-not-remove-degenerate-face
  - atlas-steinberg-spare-index-independence
  - leavitt-prefixes-form-exponential-heisenberg-packet
  - finite-positive-root-fragments-have-marked-regular-models
---

For `(EFT3)`, apply

```text
[x_1r(a),x_rs(b)]=x_1s(ab)                            (EFPX1)
```

to `(a,b)=(p,E),(q,E),(p,F),(q,F)`.  The sign of the right-hand side
controls the corresponding coordinate toggle.  Since `1=p+q`, its sign bit
is the sum of the two `p/q` bits, giving the `w` coordinate in `(EFT3)`.

The four words in `(EFT2)` are distinct reduced Leavitt normal forms: each
has one unstarred prefix and two starred suffix letters.  They are therefore
linearly independent.  Repeating at three independent target matrix entries
gives twelve independent root signs.  Canonical trace is regular on that
`C_2^12`, proving `(EFT4)`.

The return identities `(EFT5)--(EFT6)`, the roots `(EFT7)`, and the
commutator table `(EFT8)` are exactly
`leavitt-prefixes-form-exponential-heisenberg-packet`, with active corner
`A=1`, characteristic `2`, and its indices relabelled from `(1,2,3)` to
`(1,3,2)`.  Its center is therefore the original marked root `x_12(1)`.
That claim proves the spin divisibility `(EFT9)` at every depth and hence
exact finite-dimensional collapse of the marked center.

Conversely, `finite-positive-root-fragments-have-marked-regular-models`
applies to every fixed finite depth.  It provides an exact regular model in
which `J` retains trace-half negative mass.  Thus no fixed depth, including
the full depth-one E/F continuation, can supply a dimension-independent
normalized-HS obstruction.  The only new phenomenon after adjoining the
return rows is unbounded coherent depth.
