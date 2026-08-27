---
rg: 2
id: atlas-five-row-blowup-branch-is-impossible
kind: claim
title: Five-row coercivity and the 19243 commutant gap exclude every normalized blow-up escape
distinct_from:
  atlas-five-row-lift-failure-dichotomy: that splits failure into a macroscopic branch and a vanishing-signal blow-up branch; this eliminates the latter branch.
  atlas-19243-centrality-forces-s3-distance: that gives the zeroth-order gap from the S3 commutant; this combines it with five-row linear coercivity and finite-H polar rounding.
  atlas-aligned-quotient-spectrum-cannot-reach-low-defect: that explains why a derivative calculation near the aligned manifold cannot reach low-defect frames; this proves the stronger fact that five-row additive energy cannot vanish on a low-interior-defect sequence.
---

Use

```text
A(U)=sum_(j in {0,11,30,44,55}) ||rho(z_j)U||_2^2,
e_int(U)=||pi_U(c_19243)-1||_2.                       (FBI1)
```

There is a multiplicity-independent constant `D<infinity` such that every
regular amplified relative chart unitary satisfies

```text
sqrt(2) <= e_int(U)+D sqrt(A(U)).                     (FBI2)
```

Consequently the normalized blow-up alternative of
`atlas-five-row-lift-failure-dichotomy` is impossible.  More precisely,

```text
e_int(U_n)=o(sqrt(A(U_n)))  and  A(U_n)->0            (FBI3)
```

cannot hold.

It follows that `atlas-five-row-operator-phase-lift` is equivalent to the
purely qualitative assertion

```text
there is no tracial matrix-ultraproduct common-orbit model in which
the six nonlinear relators vanish and A(U)>0.          (FBI4)
```

Thus the proposed derivative test on the `H`-commutant is vacuous: on that
entire commutant the interior defect is already exactly `sqrt(2)`, so there
is no exact interior-zero base point at which to test a derivative.

## Proof

Let `H=diag(GL_3(2),1)` and let `E_H` be averaging of the conjugation action
of `H` on the matrix space.  It is the Hilbert--Schmidt orthogonal projection
onto the commutant `N=rho(H)'`.  The fixed four transvections generate `H`.
Their finite Cayley Laplacian has a positive spectral gap `kappa_H` on the
orthogonal complement of `N`, independent of the external multiplicity.
Combining this Poincare inequality with
`regular-atlas-linearized-h-coercivity` gives

```text
||U-E_H(U)||_2^2 <= (C_lin/kappa_H) A(U).             (FBI5)
```

Put `X=E_H(U)`.  Since `E_H` is a unital completely positive contraction,
`X` is a contraction in the finite-dimensional algebra `N`.  Extend its
polar partial isometry to a unitary `V in N`.  Orthogonality of the
conditional expectation and `(1-s)^2<=1-s^2` for `0<=s<=1` give

```text
||U-V||_2^2
 =||U-X||_2^2+||X-V||_2^2
 <=2||U-X||_2^2
 <=(2C_lin/kappa_H)A(U).                              (FBI6)
```

The collision subgroup `K_19243~=S3` lies in `H`, so `N` is contained in
the unitary `K_19243` commutant.  The exact calculation
`atlas-19243-centrality-forces-s3-distance` says

```text
||pi_V(c_19243)-1||_2=sqrt(2)                         (FBI7)
```

for every such `V`, and that the interior word is `16`-Lipschitz in the
relative unitary.  Hence

```text
sqrt(2)
 <=e_int(U)+16||U-V||_2
 <=e_int(U)+16 sqrt(2C_lin/kappa_H) sqrt(A(U)).        (FBI8)
```

This is `(FBI2)` with `D=16 sqrt(2C_lin/kappa_H)`, and immediately excludes
`(FBI3)`.

For the final equivalence, one direction is immediate from the five-row
inequality.  Conversely suppose `(FBI4)` holds but no uniform five-row
constant exists.  The failure dichotomy leaves either a macroscopic escape
or a normalized blow-up escape.  The former contradicts `(FBI4)` and the
latter contradicts `(FBI2)`.  Therefore the uniform inequality holds.

## Strategic consequence

The exact side is now the whole Atlas five-row problem at the qualitative
level: exclude a positive-energy exact solution in a tracial matrix
ultraproduct.  Exact finite quotient searches test only constant finite
models of this obstruction.  Residual finiteness of the six-relator quotient
would instead produce such a finite model and **refute** the five-row lift.
