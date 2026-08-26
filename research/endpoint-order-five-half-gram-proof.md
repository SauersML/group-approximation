---
rg: 2
id: endpoint-order-five-half-gram-proof
kind: route
title: Compute the GL4 endpoint actor, its half Gram, and the signed-sheet exits
target: endpoint-order-five-actor-has-half-gram
requires:
  - endpoint-whitehead-hecke-flag-trichotomy
  - native-whitehead-hecke-head-has-order-seven-anchor
  - endpoint-detector-cell-retains-coboundary-gauge
---

Prefix cancellation and ordinary non-opposite Steinberg collection give
the images in `(OFG4)`.  In the ordered exponent basis
`(C_3,s,t,s')`, they are the two matrices whose columns are

```text
M=(1+4, 4, 1+2, 8),              W=(1, 8, 4, 2)       (1)
```

in four-bit notation.  Exact multiplication gives orders `7,2,5` for
`M,W,WM`.  Breadth-first closure of these sixteen-bit matrices has order
`20160`, and the orbit of any nonzero vector has size `15`.  Since

```text
|GL_4(F_2)|=(16-1)(16-2)(16-4)(16-8)=20160,
```

this proves `(OFG5)` and transitivity without identifying the actor by an
order coincidence alone.

For any representation, restrict to `V` and decompose into its sixteen
joint characters.  Conjugation by `GL_4(F_2)` preserves multiplicities and
has precisely the zero orbit and the nonzero orbit.  The equations

```text
C_3=-1, s=+1
```

select `2^2=4` nonzero characters; adding `s'=+1` selects `2`.  This proves
`(OFG7)`.  Conjugating the first projection by `W` replaces the `s=+1`
condition by `s'=+1`, so multiplication of the commuting spectral
projections proves `(OFG8)`.

The same exact sparse collection gives `(OFG9)` and `(OFG11)`.  A nonzero
power `M^j` generates the same cyclic group as `M`, so if it normalized
`K_1`, then `M` would normalize `K_1`, contrary to `(OFG9)`.  The exact
four-bit closure contains eight elements with the action `(OFG10)`.  Lift
the shortest positive `W,M` word for each element back to the literal
Leavitt matrices and conjugate all five generators of `K_1`.  In every
case at least one image leaves `K_1` or has the wrong character.  Finally,
if `k in K_1` and `kg` normalized `K_1`, then so would `g`, because `k`
already normalizes `K_1`.  This proves the dressing fence.

All matrix and finite-actor assertions are reproduced by
`experiments/endpoint_fine_collision_odd_mixed_audit.py`.  Its native
orientation is `J_2=What_(8,9;2)`.  A second faithful sparse Leavitt replay
checks `M^7=(WM)^5=1` without bounding prefix length; this prevents the
four-bit root action from being misread as a finite-prefix quotient.  The
script runs only through MSI and its exact four-bit closure finishes in
under four seconds.  No numerical tolerance or random search occurs.
