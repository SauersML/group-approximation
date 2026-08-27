---
rg: 2
id: atlas-gl6-repeated-affine-collision-collapse-proof
kind: route
title: Collapse every homogeneous-affine Q1920 multiplicity algebra
target: atlas-gl6-repeated-affine-collision-collapse
requires:
  - atlas-q1920-is-radial-holonomy-extension
artifacts:
  - experiments/atlas_a4_q1920_module_structure.g
  - experiments/atlas_a4_q1920_affine_homogeneous_coordinates.sage
  - experiments/atlas_a4_q1920_gl6_repeated_affine_seam.g
  - research/artifacts/atlas-a4-gl6-repeated-affine-collision-gbnp.json
---

Start with the exact large-rectangle presentation

```text
Q=<r,y,u,b |
 r^3,y^3,u^2,b^2, urur, byby,
 (r^-1 b)^3,(uy)^3,((ur)y^-1)^3,(rby)^3>.
```

The complete degree-at-most-twelve faithful census has exactly two marked
order-1920 quotients.  In each, the characteristic radical `V=O_2(Q)` has
order 32, the quotient is `A5`, and GAP returns exactly four conjugacy
classes of complements `K` to `V`.  The verifier reconstructs rather than
hard-codes these eight marked affine actions.  For `g in Q`, its action on
`V` gives a `5 x 5` linear matrix `M_g`.  Writing `g=v_g k_g` with `v_g in V`
and `k_g in K` gives the homogeneous row matrix

```text
H_K(g) = [ M_g       0 ]
         [ v_g M_g   1 ].                              (GL6M-2)
```

For all eight slices the four displayed matrices satisfy every presentation
relator and generate a group of order 1920.

Fix a computed basis `E_0,...,E_(d-1)` of `End_A(H_K)`, where
`A=<r,u>~=S3`.  Exact linear algebra gives `d=6` or `8`, depending on the
complement class.  Every A-central operator on `H_K^m` has the unique form

```text
C = sum_i E_i tensor X_i,        X_i in M_m(F2).        (GL6M-3)
```

Let `R=F2<x_0,...,x_(d-1)>` be the free associative algebra; in particular,
the multiplicity coefficients are not assumed to commute.  Substitute the
generic matrix `C_R=sum E_i x_i` into the three relations `(GL6M-1)`.  Matrix
evaluation `x_i -> X_i` shows that the resulting two-sided ideal represents
the collision problem for every multiplicity `m`, with no rank hypothesis.

GBNP 1.1.0 first computes a strong two-sided Groebner basis for
`C_R^2=I,(C_R T)^3=I`.  In every slice this leaves exactly two residual free
parameters.  Reducing the collision entries modulo that base ideal gives two
linear normal forms:

```text
slice (marking,K)       d       collision normal forms
(1,1)                   8       x0, x2
(1,2)                   6       x0, x3
(1,3)                   8       x0, x3+x0+1
(1,4)                   6       x0, x1
(2,1)                   6       x0, x1
(2,2)                   8       x2, x3
(2,3)                   6       x1, x1+x0+1
(2,4)                   8       x3, x5.                (GL6M-4)
```

Adjoining those two forms makes the full strong basis the coordinate ideal
of the identity matrix in every slice.  Equivalently every normal form
`x_i-alpha_i`, where `(alpha_i)` are the coordinates of `I_6`, is zero.
Thus any matrix evaluation has `C=I`, at every `m`.  This proves the claim.

The four complement classes are also the automorphism-orbit firewall.  If an
affine action with stabilizer `K` is precomposed by `alpha in Aut(Q)`, its
origin stabilizer is `alpha^-1(K)`, another complement.  Conjugating that
complement inside `Q` only changes the homogeneous basis.  Hence the eight
slices exhaust the two marked affine-natural actions and all their twists.
