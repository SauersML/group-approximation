---
rg: 2
id: agent-aggregate-escape-a4-fourier-corner-proof
kind: route
title: Split the A4 product displacement into four positive Fourier overlaps
target: agent-aggregate-escape-a4-bridge-lands-at-bcl-root-gate
requires: []
---

On the range of `E`, the subgroup `H` acts trivially and `J` acts by `-1`, so
`(ABR2)` gives `(z_1z_2-1)E=-2E`.  Write

```text
(z_1z_2-1)E=z_1(z_2-1)E+(z_1-1)E.
```

Left multiplication by `z_1` preserves Hilbert--Schmidt norm.  Squaring the
triangle inequality proves `(ABR4)`.

For an order-three unitary `z`, functional calculus gives

```text
(z-1)^*(z-1)=3(R_omega+R_(omega^2)).
```

Cyclicity of trace proves `(ABR5)`.  The four nonnegative overlaps have sum
at least `2 tau(E)/3`, so their maximum is at least `tau(E)/6`.

This is where the proof stops.  Although each `R_(i,omega)` belongs to the
finite `A4` factor and `E` belongs to the finite old subgroup, together they
live in the group algebra of the amalgamated free product

```text
<H,J> *_(<hJ>) A4,
```

not in a finite-dimensional bridge algebra.  The support of
`R_(i,omega) E R_(i,omega)` in a von Neumann representation is therefore not
a fixed polynomial group-algebra idempotent.  Its central support is likewise
representation-dependent.  Consequently `(ABR6)` is a four-piece scalar
overlap compiler only; it does not name a coefficient idempotent for the BCL
root.  Any payload-to-root theorem must add a genuinely new mixed relation,
not merely take the support of this overlap.
