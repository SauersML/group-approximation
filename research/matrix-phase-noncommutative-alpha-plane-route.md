---
rg: 2
id: matrix-phase-noncommutative-alpha-plane-route
kind: claim
title: Prove a noncommutative alpha-plane energy inequality for arbitrary block phases
distinct_from:
  matrix-phased-translations-exact-identity-scalarize: that assumes zero identity energy and diagonalizes exactly; this asks for a joint inequality when both sampled energies are nonzero.
  pauli-block-phases-have-uniform-two-matching-soundness: that uses discrete Pauli labels and a symplectic form; this allows arbitrary unitary blocks with no finite label model.
---

OPEN.  The arbitrary block-diagonal conjugator sector has one self-contained
formulation.  For `R:K->U(d)`, define

```text
I(R)=E_(x,y)||R_y R_x^*-R_x R_y^*||_2^2,                    (NC1)

A(R)=E_(x,b)||R_(x+b)R_x^*
                 -R_(x+(1+alpha)b)R_(x+alpha b)^*||_2^2,    (NC2)

F(R)=E_(x,a,b)||R_(x+b)R_x^*
                 -R_(x+a+b)R_(x+a)^*||_2^2.                (NC3)
```

For the tables `(MP1)`, these are exactly the identity-matching,
alpha-matching, and complete cross-commutator energies.  Prove, or disprove,

```text
F(R) <= C(I(R)+A(R))                                         (NC4)
```

with universal `C`, independent of `n,d`.  This would settle every
single-block-PVM orbit and leave only mixing between inequivalent `X`-orbits.

The endpoint already has a positive noncommutative Fourier formula.  With
normalized Fourier matrices

```text
M_xi=E_x (-1)^<xi,x> R_x,
```

operator-valued Parseval gives

```text
F(R)=2(1-sum_xi tr((M_xi M_xi^*)^2)).                        (NC5)
```

Thus `(NC4)` is a derandomized matrix-valued `U^2` inequality: the identity
orientation correlation plus the alpha-plane quartic correlation must control
the complete positive Fourier fourth moment.

## Closed boundary cases

- `I(R)=0`: `matrix-phased-translations-exact-identity-scalarize` gauges the
  blocks into commuting reflections and gives `(NC4)` with `C=27/2`.
- Signed Pauli `R_x`: `pauli-block-phases-have-uniform-two-matching-soundness`
  proves `(NC4)` by correcting the discrete quotient labels, killing the
  symplectic cocycle, and scalarizing the center.
- Scalar reflections: `phased-translations-reduce-to-alpha-plane-test` is the
  Kaufman--Sudan affine single-orbit inequality.

## Attempts

- **Round `(NC1)` before using `(NC2)`.**  This is false uniformly.  Pauli
  reflections realizing a fixed-degree regular anticommutation graph have
  `I(R)=O(1/N)` but constant average distance from every commuting family.
  The two energies must enter one joint square function.
- **Apply scalar single-orbit soundness to matrix coefficients.**  The sampled
  equation is linear in edge quotients `R_yR_x^*`, but those quotients obey a
  noncommutative cocycle.  Individual coefficients do not satisfy the Boolean
  parity constraint, and summing coordinatewise loses the matrix dimension.
- **Use only the long multiplicative cycle of `alpha`.**  Its spectral gap
  tends to zero.  Scalar soundness survives because of affine-orbit
  self-correction, not because that cycle expands; a valid operator proof must
  retain the four-point cocycle identities.
- **Direct Fourier Cauchy--Schwarz.**  The alpha quartic form is an involutive
  mixing of pairs of Fourier matrices.  Plain Cauchy--Schwarz bounds it by one
  and does not recover the diagonal positive fourth moment in `(NC5)`.  The
  missing input is precisely the orientation energy `(NC1)`.
