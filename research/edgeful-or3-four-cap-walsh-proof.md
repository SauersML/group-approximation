---
rg: 2
id: edgeful-or3-four-cap-walsh-proof
kind: route
title: Sum four affine caps and Fourier-transform their character signs
target: edgeful-or3-four-cap-walsh-packet
requires:
  - edgeful-one-ghost-fano-relation
---

Each `H_l` in `(OCW1)` has four points.  Counting the caps containing a
fixed nonzero `x` gives three for `wt(x)=1`, two for `wt(x)=2`, and one for
`x=111`, proving `(OCW2)` and total dimension `16`.  Since `l` is never a
coordinate functional, each coordinate is nonconstant on `H_l`, with two
zeros and two ones.  Every cap block and hence their direct sum is balanced.

On `H_l=t_l+V_l`, the coordinate sign is

```text
(-1)^(x_j)=(-1)^((t_l)_j) (-1)^((e_j|V_l)(u)).
```

Fourier transform converts multiplication by the character `e_j|V_l` into
translation by that character, proving `(OCW3)`.  A nonzero translation of
the four-element group `V_l^*` is two transpositions and has zero diagonal.
The Walsh matrices and these character signs lie in the finite two-qubit
Pauli algebra.  More explicitly, the negative central-character corner of
the extraspecial two-qubit Pauli group is `M_4(C)`.  Tensoring that finite
group with `C_2^2` gives four central character blocks, proving `(OCW3a)`.
The rank-one character idempotents of the Pauli algebra give the four
assignment atoms in each block, while its full matrix corner contains the
Walsh conjugator.

Two coordinate matchings on the `l` block coincide precisely when

```text
e_i|V_l=e_j|V_l
iff e_i+e_j lies in V_l^perp=<l>
iff l=e_i+e_j.                                          (OCW6)
```

This gives the three coincidences in `(OCW4)`.  On the corresponding cap,
`x_i+x_j=1`, so the two signed operators are negatives.  For `l=111`, the
three restrictions are the three nonzero elements of the two-dimensional
dual, proving `(OCW5)`.  Conjugation by the same diagonal phase unitary on a
block gives `(OCW7)` and preserves all these exact equalities term by term.

Finally, self-adjointness identifies the two orientations of one matching
edge by adjunction.  It does not identify equations belonging to distinct
logical marginals or distinct global target words, which proves the stated
duplicate-equation audit.
