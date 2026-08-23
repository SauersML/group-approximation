---
rg: 2
id: atlas-five-row-operator-phase-lift
kind: claim
title: Five saturated Atlas rows lift nonlinear phase defect to linear covariance energy
distinct_from:
  atlas-linear-energy-controlled-by-full-packet-defect: that asks to control the sum of all 234 linearized boundary rows by all 234 nonlinear defects plus the interior separator; this keeps only the five rows already certified to saturate the covariance tangent kernel.
  atlas-boundary-tangent-covariance-coercivity: that bounds covariance by the five linearized rows and is already global in the chart unitary; this asks for the missing nonlinear-to-linear comparison for those rows.
  atlas-a4-holonomy-coherence-gap: that exact-regular local-network ceiling is refuted by the multiplicity-two frame; this includes the full-atlas interior consequence which the local frame does not satisfy.
---

**OPEN.**  Let

```text
J={0,11,30,44,55}                                     (FPL1)
```

be the five first-boundary indices whose integral derivatives already have
the full `H=GL_3(2)`-fixed kernel.  For each `j in J`, write

```text
l_j(U)=||rho(z_j)U||_2,                               (FPL2)
```

with the fixed integral row `z_j in Z[A8]`, and let

```text
e_j(U)=||pi_U(s_j)-1||_2,
e_int(U)=||pi_U(c_19243)-1||_2.                        (FPL3)
```

Prove one multiplicity-independent constant `C_5<infinity` such that every
relative chart unitary `U in U(20160k)` satisfies

```text
sum_(j in J) l_j(U)^2
 <= C_5 [sum_(j in J)e_j(U)^2+e_int(U)^2].             (FPL4)
```

This is the smallest presently certified finite operator-valued phase
inequality sufficient for the strict two-`S3` ceiling.  The left side is a
five-row quadratic form in the common relative unitary; the right side
contains the corresponding five nonlinear transported-phase products and
one interior commutator.  No local representation-type variable remains.

## Exact-model audit

The known multiplicity-two frame does not refute `(FPL4)`.  It is exact on
the thirty shortest A4 context rows and on collision `19243`, but those are
not the five first-boundary words `(FPL1)` together with the full-atlas
interior commutator.  Its refutation of
`atlas-a4-holonomy-coherence-gap` therefore cannot be transferred to this
claim or to `atlas-two-s3-energy-ceiling-below-19243-floor`.

The characteristic-two affine boundary model is the relevant calibration:
it kills all 234 boundary defects while retaining positive covariance, but
the interior commutator is nontrivial.  Thus it proves that `e_int` cannot be
deleted from `(FPL4)` and supplies a finite lower bound on any admissible
constant; it does not make the right side vanish.

## Why this is still nonlinear

For one row, the exact atlas word is a product of transported relative
phases, whereas `rho(z_j)U` is their signed sum.  Ordinary telescoping bounds
the product by the sum in the opposite direction.  Reversing it in
normalized Hilbert--Schmidt norm cannot follow from a Taylor remainder,
because products of two HS-small terms need operator-norm control.  The
interior commutator must rule out precisely the large noncommutative phase
cancellations which survive the five boundary products.

## Attempts

1. **Telescope the five products.**  This proves the reverse inequality,
   bounding each nonlinear defect by a sum of phase increments.  Reversing
   it loses operator norm on the quadratic cross terms and is unavailable in
   normalized HS norm.
2. **Delete the interior row.**  The exact characteristic-two affine model
   kills all five boundary products while retaining positive linearized
   energy, so a boundary-only inequality is false.
3. **Use the exact A4 coherence transducer.**  It losslessly identifies the
   three local phase sectors, but a multiplicity unitary remains free around
   a cycle.  The unresolved operation is to make `c_19243` pay that one
   operator-valued loop phase rather than only its scalar character.
