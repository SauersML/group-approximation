# sk-malcev: ledger (simple_kazhdan_sofic_group.tex at 9047d0d3c, md5 274f19367f7f706b05c017af721c3884)

## CLAIM
CLAIM Malcev printed endpoint GroupApproximation/Manuscript/SimpleKazhdanSofic/MalcevLinearResiduallyFinite.lean

## Finding: Malcev's theorem is already proved on origin
It is root-reachable (GroupApproximation.lean l.450–451 import `Algebra.Malcev` and `Algebra.MalcevLinear`), and no binder stands for a cited result.
- `GroupApproximation.exists_finite_field_hom_of_ne_zero` (Algebra/Malcev.lean:27): a nonzero element of a finitely generated domain survives in a finite field. It rests on `Algebra/FiniteTypeField` and `Algebra/IntJacobson`.
- `GroupApproximation.residuallyFinite_generalLinearGroup` (Algebra/Malcev.lean:68): GL_d(R) is residually finite for R a finitely generated domain.
- `GroupApproximation.MalcevLinear.residuallyFinite_of_fg` (Algebra/MalcevLinear.lean:191): a finitely generated subgroup of GL_d(F), F any field, is residually finite.
- `MalcevLinear.not_injective_of_not_residuallyFinite` (:231): the contrapositive, for a finitely generated group with a representation.
- Lexical scan of IntJacobson, FiniteTypeField, Malcev and MalcevLinear: no sorry, admit, axiom, `Input :` or `Statement :`.

So this lane builds only the printed endpoint with closed audits. No new theory is needed.

## Sentence ledger
| tex (9047d0d3c) | sentence | carrier | status |
|---|---|---|---|
| l.352–353 | "Finitely generated linear groups are residually finite by Malcev's theorem" (clause 1) | `SimpleKazhdanSofic.printedFGLinearResiduallyFinite : PrintedFGLinearResiduallyFinite`, plus `fgLinear_isResiduallyFinite` (the repository's `IsResiduallyFinite`) | pending probe |

- Printed generality: "linear" means an injective homomorphism into GL_d(F) for some d and some field F, at any universe levels.
- Route: Malcev's route, following the entry subring and finite residue fields.
- Census row: waits for skf-census to regenerate the census at 9047d0d3c.
