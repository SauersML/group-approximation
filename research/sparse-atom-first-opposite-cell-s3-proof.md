---
rg: 2
id: sparse-atom-first-opposite-cell-s3-proof
kind: route
title: Match the marked involution and place one standard S3 block on the selected character line
target: sparse-atom-first-opposite-cell-has-s3-amalgam-model
requires:
  - sparse-parabolic-atom-has-split-inertia
  - scalar-active-mixed-shell-has-marked-regular-model
---

In the diagonal--permutation representation on `ell^2(A^)`, the nonzero
element `a_0` has equally many `+1` and `-1` eigenlines.  Choose the negative
line `C delta_chi` and the positive line of the trivial character.  On their
span, the two matrices in `(SOF4)` are involutions and their product is a
rotation through `2 pi/3`; hence they satisfy the Coxeter braid `(SOF2)`.

On every remaining negative `u`-eigenline put the sign representation of
`S_3`, and on every remaining positive `u`-eigenline put the trivial
representation.  The resulting `S_3` representation has exactly the same
operator `u` as the original `A semidirect K` representation.  The universal
property of the amalgam `(SOF3)` therefore gives the asserted exact
finite-dimensional representation without changing any operator from the
finite character packet.  In particular `(SOF1)` remains a rank-one joint
spectral atom.

On the standard block, `P=diag(1,0)`.  The vectors spanning `Q` and `R` are

```text
q=(1/2,-sqrt(3)/2),             r=(1/2,sqrt(3)/2).
```

Their inner products with the vector spanning `P` are both `1/2`, while
`<q,r>=-1/2`.  The projection formulas immediately give

```text
PQP=PRP=(1/4)P,          QRQ=(1/4)Q,          ||QR||=1/2.
```

Adding the two rank-one projection matrices gives the last formula in
`(SOF7)`.  Since `v^2=w^2=1`, their definitions also give `(SOF6)`.
The conjugation action of `S_3` on its three transpositions is faithful and
the stabilizer of `u` is `<u>`, proving the scalar same-atom statement.

Finally, for an idempotent `q` in characteristic two, the map

```text
Phi_q(M)=I+(M-I)q
```

is the scalar-corner embedding from
`scalar-active-mixed-shell-has-marked-regular-model`.  It sends the two
elementary generators of `GL_2(F_2)` to `x_ij(q)` and `x_ji(q)`, proving
that the abstract `S_3` cell is the literal first opposite-root cell in
`(SOF8)`.
