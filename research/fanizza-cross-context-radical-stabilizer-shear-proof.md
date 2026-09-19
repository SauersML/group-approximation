---
rg: 2
id: fanizza-cross-context-radical-stabilizer-shear-proof
kind: route
title: Use the two opposite GL2 shears that fix the shared endpoint coordinates
target: fanizza-radical-tuples-have-stabilizer-shears
requires:
  - every-predicate-has-s3-equivariant-raw-radical-drop
  - fanizza-radical-charts-admit-common-symplectic-reset-subgroups
  - phase-inverting-fourth-root-lifts-opposite-pauli-shears
---

Write the outer-coordinate matrices as

```text
G_0=[[1,1],[0,1]],             G_1=[[1,0],[1,1]].       (1)
```

Both preserve the hyperbolic form `H`.  The first fixes `e_0` and satisfies
`G_0^T ell_3=ell_1`; the second fixes `e_1` and satisfies
`G_1^T ell_2=ell_3`.  Therefore their extensions by the identity on the
inner compiler coordinates and the odd chart coordinate give congruences

```text
G_0^T B_(ell_3)(x) G_0=B_(ell_1)(x),
G_1^T B_(ell_2)(x) G_1=B_(ell_3)(x)                    (2)
```

for every selector value `x`.  Equivalently, conjugation carries the twist
automorphisms as in `(XRS2)`.

Choose any common-sector witness `phi_beta` supplied by the common-reset
claim, and set

```text
phi_alpha=G_0^T phi_beta,       phi_gamma=G_1^T phi_beta. (3)
```

Equation `(2)` transports the unique radical line in every sector, so `(3)`
is one on every corresponding radical.  Hence all three kernels are
nondegenerate complements and the two shears carry them exactly as stated.

The phase-corrected packet lifts do not introduce a hidden sign.  The lift of
`G_0` fixes every generator in the `e_0` half, while the lift of `G_1` fixes
every generator in the `e_1` half.  Each `r_(a,j)` is a product solely of
generators in that fixed half and contains no central root, proving the exact
word equalities in `(XRS2)`.  Both twist functionals take value one on their
shared word, which proves `(XRS3)`.

For completeness of the blockwise criterion, decompose an outside vector as
`r=w+cq`, where `q` is the odd form's radical, `phi(q)=1`, and `w` lies in the
reset hyperplane.  Equations `(2)--(3)` carry `q,w,c` to their target values.
The vectors for distinct marked atoms are independent.  They are isotropic
because they lie in one outer coordinate, and adding the radical does not
change any pairing.  The finite-field audit verifies these identities and
the resulting uniform joint Pauli multiplicities in every individual
selector block.
