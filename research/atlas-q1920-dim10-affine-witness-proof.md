---
rg: 2
id: atlas-q1920-dim10-affine-witness-proof
kind: route
title: Replay the exact ten-dimensional Q1920 affine collision witness
target: atlas-q1920-dim10-f3-reduced-seam-has-affine-signal
requires: []
artifacts:
  - experiments/verify_atlas_q1920_dim10_affine_witness.py
  - experiments/atlas_a4_q1920_f3_seam_export.g
  - experiments/atlas_a4_q1920_f3_dim10_affine_witness.sage
  - research/artifacts/atlas-a4-q1920-f3-dim10-affine-seam.json
---

The standard-library verifier contains the four exported `10` by `10`
matrices `r,u,t,s`, the collision involution `c`, and the translation row
`z`, all over `F3`.  Thus the certificate has no generated-file, Sage, GAP,
or random-basis dependency.  It defines `y=t^-1` and `b=s t` and checks the
nineteen displayed matrix words directly.  These are the ten defining
`Q1920` words, the eight local `F` and `J` seam words, and collision

```text
t c s c t^-1 c s t c = 1.
```

Row reduction gives

```text
dim Fix_<r,u>(F3^10) = 3,
dim End_<r,u>(F3^10) = 19.
```

The displayed `z` is nonzero and fixed by `r,u`; the displayed nonidentity
`c` commutes with `r,u`, squares to one, and sends `z` to `-z`.  Consequently
the matrices give a direct substitution into the reduced collision system.
This route does not need the discovery Groebner basis: the archived basis
records how the witness was found, while direct evaluation proves its
existence.

There is also an independent irreducibility certificate.  Starting with the
identity and closing its `F3`-linear span under right multiplication by
`r,y,u,b` produces dimension `100`, hence the full algebra `Mat_10(F3)`.
Any common invariant subspace for the four generators is therefore invariant
under every matrix, so it is zero or all of `F3^10`.

For the finite orders, each matrix row is encoded as a base-three integer.
Breadth-first closure from the identity under every listed generator stops
only when no unseen state remains.  Since the generators are invertible and
the closure is finite, this generated monoid is the generated group.  The
exact counts are

```text
|<r,y,u,b>| = 1920,       |<r,z,c,u>| = 36,
|<t,s,c>| = 24,           |<r,z,b>| = 324,
|<r,y,u,b,c>| = 30720.
```

Finally, conjugating the translation `z` by the five linear generators and
row reducing their orbit produces rank `10`.  The affine group therefore
contains the entire translation kernel `F3^10`; its projection is the
enumerated order-`30720` linear group.  As it lies in the corresponding
affine semidirect product, its kernel is exactly that translation group, and

```text
|<r,y,u,b,c,z>| = 3^10 * 30720 = 1813985280.
```

Both protected elements are nonidentity.  Direct multiplication also gives
`(z b)^3 != 1`, while the exact forward subgroup order is `324`, not `144`.
The witness therefore establishes precisely the reduced-seam signal and not
a full-packet carrier: the omitted `C144` attachment is essential.
