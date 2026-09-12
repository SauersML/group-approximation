---
rg: 2
id: atlas-aligned-word-jacobian-has-full-multiplicity-absorber
kind: claim
title: An aligned Atlas word Jacobian leaves a full multiplicity reservoir in every compulsory block
distinct_from:
  atlas-phase-jacobian-has-invertible-gauge-kernel: that uses only the scalar tangent iU and rules out shrinkage of the whole Jacobian kernel; this computes the complete multiplicity amplification of that tangent inside every regular-A8 Fourier block.
  atlas-a8-mixed-block-transport-has-permutation-models: that realizes arbitrary scalar block transports by exact unitaries; this is a relation-sensitive statement about the joint derivative of every actual two-chart word at an aligned exact frame.
  atlas-a8-hall-deficit-needs-439-forbidden-blocks: that counts whole-block deletions in an arbitrary support graph; this proves that the aligned word Jacobian cannot make a surviving block contribute only a proper multiplicity range.
---

**ESTABLISHED EXACT WITHIN-BLOCK ABSORBER.**  Let

```text
rho = Reg(A8) tensor I_k
```

and let `U_0` be an exact aligned relative chart frame: conjugation by `U_0`
permutes the two labelled regular-`A8` copies.  For any finite family `W` of
alternating two-chart group words, left-trivialize their differentials at
`U_0` and intersect their kernels.  On the regular Wedderburn decomposition
the resulting joint Jacobian has the form

```text
D_W = direct_sum_(tau,sigma)
      (D_W^(tau,sigma) tensor I_(Hom(M_sigma,M_tau))),       (AJM1)
```

where

```text
Reg(A8) tensor C^k
 = direct_sum_sigma V_sigma tensor M_sigma,
dim M_sigma=d_sigma k.                                      (AJM2)
```

For every nonzero aligned block of `U_0`, write its representation part as
`A_sigma:V_sigma->V_(alpha sigma)`.  Scalar phase invariance puts
`A_sigma` in the corresponding finite kernel of `(AJM1)`.  Consequently

```text
A_sigma tensor B  in ker D_W
for every B in Hom(M_sigma,M_(alpha sigma)).                (AJM3)
```

Let `p_(sigma,a)` and `q_(alpha sigma,b)` be minimal Fourier projections.
If the scalar coefficient `(A_sigma)_(b,a)` is nonzero, then

```text
span{q_(alpha sigma,b) T p_(sigma,a) x:
     T in ker D_W, x in p_(sigma,a)H}
   =q_(alpha sigma,b)H.                                     (AJM4)
```

Thus an aligned Jacobian block is all-or-zero at the multiplicity-range
level.  It never deletes one proper common subspace inside a surviving
rectangular block.  Moreover the support of the aligned unitary itself is
contained in this all-or-zero graph, so that graph carries the complete
regular marginal transport and has no Hall deficit.

This applies to the actual five boundary words, collision `19243`, their
commutator, and indeed every fixed family of ordinary Atlas kernel words.
Hence neither the full word Jacobian nor any block restrictions
`q_u dR_j(U_0) p_v` can provide the sought finite-matrix-only range deletion
at an exact aligned frame.  A successful range certificate must be genuinely
nonlinear and selected away from the aligned tangent stratum (for example
from finite singular values of a secant operator); adding more word rows to
the same Jacobian cannot remove the reservoir `(AJM3)`.

