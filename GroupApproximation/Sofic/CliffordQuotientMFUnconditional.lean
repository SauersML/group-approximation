import GroupApproximation.Sofic.CliffordBSAmenableMF
import GroupApproximation.Sofic.CliffordBSPrintedRoute

/-!
# The sharpness paragraph's conclusion, with the Tikuisis--White--Winter binder removed

`non_mf_groups_exist.tex`, `\section{The cyclic comparison}`
(`\label{sec:necessity}`), paragraph *Sharpness of the Kazhdan hypothesis*
(grep `"hence MF by"`, never a line number).  Proof-ledger rows `CY.10`,
`CY.12` and `CY.13` all record the same exposed hypothesis,

    tww : ∀ (G : Type) [Group G] [Countable G], IsAmenable G → IsOperatorMF G

which `Sofic.CliffordBSPrintedRoute` carries in the binder of every theorem
that consumes it.  This file removes that binder from everything except the
one clause that genuinely asserts it.

## What the binder was buying, and what it is still needed for

The printed chain is: the realized Clifford quotient is amenable (steps 1--4),
*hence MF* (step 5, the citation), hence composing a faithful representation of
it with the quotient map detects `w_BS` (step 6), hence
`w_BS ∉ Res_MF(E_BS)`.

Only the middle link needs the citation, and only for its own sake: the
*endpoint* — a corona representation of `E_BS` that does not kill the mark —
is supplied outright by `Sofic.CliffordBSAmenableMF`, which exhibits an
explicit sequence of monomial matrix models of the seven printed relators in
which the mark is the scalar `-1`.  So every statement below is the printed
route's conclusion with no hypothesis at all.

What is **not** removed, and must not be reported as removed:

* `CliffordBSPrintedRoute.isOperatorMF_realizedQuotient`, the printed sentence
  "is therefore amenable, hence MF" — its subject is MF-ness of the realized
  Clifford quotient itself, which nothing in this repository proves.  Row
  `CY.10`'s middle clause keeps its binder;
* `INT.11`, the general statement that every countable amenable group is MF,
  quantified over all such groups, used in `\section{Consequences}`.

`Analysis.AmenableQuasidiagonal` records why the first cannot be reached
cheaply: permutation operator-norm models have defect `0` or at least `1`, so
they certify exactly the LEF groups, and the realized quotient is provably not
LEF (`CliffordBSAmenableMF.realizedQuotient_elementary_routes_closed`).  The
models that do the work below are monomial rather than permutation matrices,
which is exactly the room that dichotomy leaves open, and they are models of
the *relators*, not a faithful representation of the quotient — which is why
they settle the conclusion and not the sentence.

## Relation to the two modules it draws on

Nothing here is a new mathematical step: each declaration is the printed
route's statement with the binder deleted, proved by delegating to the
unconditional route.  The point of restating them is that the ledger rows
grade the printed route's declarations, and those carry a hypothesis that the
conclusion does not need.  No declaration here may be read as certifying the
printed sentence of step 5; see the module docstring of
`Sofic.CliffordBSAmenableMF`, whose doctrine this file follows.
-/

namespace GroupApproximation
namespace CliffordQuotientMFUnconditional

open LiteralCyclicCalibration

/-! ## Step 6's endpoint, without the binder -/

/-- **The paragraph's `Θ`, unconditionally.**  There is a homomorphism of
`E_BS` into the unitary group of a cofinite norm-matrix corona that does not
kill the marked word.

This is exactly the conclusion of
`CliffordBSPrintedRoute.exists_coronaRepresentation_mark_ne_one`, whose proof
composes a faithful representation of the realized quotient with the quotient
map and therefore needs step 5.  Here the corona representation is the
explicit monomial model of `Sofic.CliffordBSAmenableMF`, which is a
representation of `E_BS` itself and factors through no MF group. -/
theorem exists_coronaRepresentation_mark_ne_one :
    ∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ Theta : LiteralGroup →* NormMatrixCoronaUnitary X, Theta mark ≠ 1 :=
  ⟨CliffordBSAmenableMF.site, CliffordBSAmenableMF.card_site_pos,
    CliffordBSAmenableMF.coronaRep, CliffordBSAmenableMF.coronaRep_mark_ne_one⟩

/-! ## Row `CY.13`, and the invisibility clauses

These four statements — `mark_not_coronaMFInvisible`,
`mark_not_actualCoronaMFInvisible`, `mark_notMem_coronaMFResidual` and
`mark_notMem_normMFResidual` — together with `realizedQuotient_isAmenable`
were once restated here under the same names, each proved by delegating to
`Sofic.CliffordBSAmenableMF`.  They are **not** restated any more, and the
aggregate below cites the base module directly.

The reason is mechanical rather than editorial: the kernel audit's `DUPLICATE`
detector keys on the *type* of a declaration and ignores its proof term
(`scripts/Audit/Scan.lean`, `let key := toString ci.type`).  A wrapper whose
proof is literally the base theorem's name is therefore still a second
declaration of the same proposition, and delegation cannot clear the finding —
only removing one of the two names can.  The base module is the one that keeps
them: it is the badged module for the sharpness paragraph and it carries the
monomial models that do the work.  Nothing outside this file ever referred to
the wrappers, and no badge, `notes/NON_MF_CLAIM_DECLS.txt` entry, proof-ledger
row or pinned signature named any of them. -/

/-! ## The paragraph, minus its one citation -/

/-- **The sharpness paragraph's conclusion, with no hypothesis.**

Read against `CliffordBSPrintedRoute.manuscriptSharpnessPrintedRoute`, which
proves the same conjuncts plus `IsOperatorMF RealizedQuotient` from the binder
`tww`: every clause below is there, and the one clause omitted is the one the
binder asserts.  That is the precise measure of what the citation contributes
to this paragraph — the intermediate sentence, and nothing downstream of it.

The solvability clauses of the printed chain (`isSolvable_BSLike`,
`LiteralDyadicCalibration.affine_isSolvable`) are unconditional in the printed
route already and are not restated. -/
theorem manuscriptSharpnessConclusionUnconditional :
    Amenability.IsAmenable RealizedQuotient ∧
      quotientMap mark ≠ 1 ∧
      (∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
        ∃ Theta : LiteralGroup →* NormMatrixCoronaUnitary X, Theta mark ≠ 1) ∧
      (mark : LiteralGroup) ∉ coronaMFResidual LiteralGroup ∧
      (mark : LiteralGroup) ∉ normMFResidual LiteralGroup :=
  ⟨CliffordBSAmenableMF.realizedQuotient_isAmenable, quotientMap_mark_ne_one,
    exists_coronaRepresentation_mark_ne_one,
    CliffordBSAmenableMF.mark_notMem_coronaMFResidual,
    CliffordBSAmenableMF.mark_notMem_normMFResidual⟩

end CliffordQuotientMFUnconditional
end GroupApproximation
