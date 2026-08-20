---
rg: 2
id: schur-predicate-coefficient-couples-to-polynomial-wall
kind: claim
title: Couple the forbidden Schur Reynolds coefficient to the explicit polynomial-compressor wall
distinct_from:
  polynomial-compressor-has-explicit-finite-quotient-wall: that constructs the fixed wall `rho(A)' minus rho(B)'`; this must place the predicate-dependent coefficient inside it in every marked microstate.
  packet-kazhdan-commutant-placement-decouples: that refutes independent tensor placement; this requires a named covariance relation which fails in exactly that countermodel.
  schur-packet-as-positive-density-compressor-wall: that allows any property-T compressor substrate; this fixes the concrete `G^2<G^3` quotient and reduces placement to a finite coefficient-module problem.
---

For the quotient pair

```text
A={(g_0,g_1,g_0)} < B=G^3,       G=SL_3(F_2),          (SPC1)
```

from `polynomial-compressor-has-explicit-finite-quotient-wall`, choose one
fixed finite-dimensional `B`-module `rho` and put

```text
W_0=rho(A)' minus rho(B)'                                 (SPC2)
```

on adjoint space. Construct a finite coefficient-covariance attachment of
each Schur predicate packet such that, after fixed-packet exactification in
every marked matrix microstate:

1. the canonical forbidden core of `R_Af-R_Bf` maps into the compressed-low
   spectral copy of `W_0` with loss at most `C delta`;
2. its image is orthogonal to the original-low spectral space up to the same
   density loss;
3. on every allowed selector sector the coefficient lies in `rho(B)'`, so no
   allowed mass is charged;
4. the relation fails in the tensor-decoupled packet/compressor model; and
5. the exact non-CE tracial BCS representation extends across the attachment.

Because `(SPC1)` and all packet groups are fixed and finite, the remaining
algebraic part is a finite bimodule/intertwiner search. The hard condition is
universality: the covariance must force the placement in every marked
representation, not merely exhibit one distinguished module. A positive
solution supplies the wall inclusion `(SPW1)`; a regular-module or induced-
sector counterrepresentation refutes the proposed attachment.

## Attempts

- **Bare commutation. Dead.** It admits the independent tensor-factor model.
- **Finite quotient wall. Solved.** The pair `(SPC1)` and a positive-density
  wall are explicit.
- **Literal identification of a packet projection with a relator defect.
  Dead.** `embedded-packet-projection-has-no-relator-ideal-certificate`
  excludes it while the packet embeds.
- **Coefficient covariance. Active.** Search for a relation on packet
  implementers and the first/third `G` factors whose induced adjoint
  intertwiner is in `W_0` exactly on the Schur rank-jump sector.
