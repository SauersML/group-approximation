import GroupApproximation.Sofic.CliffordQuotientMFUnconditional
import GroupApproximation.Analysis.AmenableMFInput

/-!
# `CY.12c`: "the realized Clifford quotient, being amenable, is itself MF"

`non_mf_groups_exist.tex`, `\section{The cyclic comparison}`
(`\label{sec:necessity}`), paragraph *Sharpness of the Kazhdan hypothesis*
(grep `"hence MF by"`, never a line number --- the file is edited
concurrently).  The aside was restored to the print on 2026-08-18 so that the
paper cites the literature it stands beside; proof-ledger row `CY.12c` grades
it `MISSING`/`literature-input` on `TWW`, with the note that "the trust
surface does not move".

That note is the claim this module turns into a theorem.  It has three parts,
and the file proves all three rather than asserting them.

## 1.  The subject of the aside is amenable, and that half is unconditional

`realizedQuotient_isAmenable`.  Proved in `Sofic.CliffordBSAmenable` through
the printed chain --- the lamp group is locally finite, the affine base is
solvable with both terms of its series carrying invariant means, the
semidirect product inherits one, and amenability passes to subgroups --- and
restated here at the group the aside is about.  Row `CY.12b` is this clause.

## 2.  The remaining half is exactly one instance of `INT.11`

`isOperatorMF_realizedQuotient_of_input` consumes
`QuasidiagonalMF.AmenableMFInput`, the general clause of the introduction, and
nothing else; `isOperatorMF_realizedQuotient_of_local` shows that even the
general clause is more than the site needs --- the *single implication*
`IsAmenable RealizedQuotient → IsOperatorMF RealizedQuotient` suffices, because
its hypothesis is already discharged.  So the aside's trust surface is one
implication at one group, and `amenableImpliesMF_of_input` identifies the
general clause with the lane's existing local binder
`CyclicBaseCalibration.AmenableImpliesMF`, so the three shapes in which the
clause occurs in this repository are one shape.

## 3.  The paragraph's conclusion consumes none of it

`aside_inert` is the ledger note as a single statement: the corona
representation of `E_BS` that does not kill the marked word --- the paragraph's
`Θ`, and the whole of what the sharpness argument delivers --- exists with **no
hypothesis at all** (`Sofic.CliffordQuotientMFUnconditional`, via the explicit
monomial models of `Sofic.CliffordBSAmenableMF`), while the aside is the
conditional clause.  Both conjuncts in one type: a reader can see that deleting
the aside would change no conclusion.

## What this module does not do

It does not badge the aside, and it does not discharge the input.  Nothing here
constructs an `AmenableMFInput`, and `Sofic.CliffordBSPrintedRoute` keeps its
inline binder --- that module deliberately writes the literature claim out in
the binder of every theorem that consumes it rather than routing through a
name, and this file does not change that.  What is added is the identification
of the shapes and the inertness statement, neither of which existed as a
theorem before.

`Algebra.AmenableMFProof` records why the conditional half cannot simply be
discharged: permutation operator-norm models have defect `0` or at least `1`,
so they certify exactly the LEF groups, and
`CliffordBSAmenableMF.realizedQuotient_elementary_routes_closed` proves the
realized quotient is not LEF.
-/

namespace GroupApproximation
namespace CliffordAsideInert

open CyclicBaseCalibration LiteralCyclicCalibration

/-! ## The unconditional half -/

/-- **`CY.12b`.**  The realized Clifford quotient of `thm:C` is amenable.
Every step of the printed chain that reaches this is machine-checked in
`Sofic.CliffordBSAmenable`; this is the clause at the group the aside is
about. -/
theorem realizedQuotient_isAmenable :
    Amenability.IsAmenable RealizedQuotient :=
  CliffordBSPrintedRoute.ambient_and_realizedQuotient_isAmenable.2

/-! ## The conditional half, and how small it is -/

/-- **`CY.12c` under the introduction's own clause.**  Granting `INT.11` ---
that every countable amenable group is operator-MF --- the realized Clifford
quotient is operator-MF.  The amenability half is discharged above; the input
is the entire external content. -/
theorem isOperatorMF_realizedQuotient_of_input (h : QuasidiagonalMF.AmenableMFInput.{0}) :
    IsOperatorMF RealizedQuotient :=
  h.mf RealizedQuotient realizedQuotient_isAmenable

/-- **The site needs far less than the general clause.**  A single implication
at a single group already suffices, because its hypothesis is a theorem.  This
is the precise sense in which `CY.12c` is one instance of `INT.11` rather than
an independent import. -/
theorem isOperatorMF_realizedQuotient_of_local
    (h : Amenability.IsAmenable RealizedQuotient → IsOperatorMF RealizedQuotient) :
    IsOperatorMF RealizedQuotient :=
  h realizedQuotient_isAmenable

/-- The general clause of the introduction gives the Clifford lane's local
binder.  Both are recorded in the repository, neither is inhabited, and this
stops a reader from counting them as two independent literature inputs.

Stated as two implications rather than one `↔` deliberately: the head of an
`↔`'s left side is what `scripts/check_non_mf_unconditional.py` reads as the
conclusion, so a biconditional between two uninhabited structures would enter
its discharge fixpoint as a premise-free producer of the left one.  Each
implication below carries the other structure as a premise, so neither name is
reported as inhabited. -/
theorem amenableImpliesMF_of_input (h : QuasidiagonalMF.AmenableMFInput.{0}) :
    CyclicBaseCalibration.AmenableImpliesMF :=
  ⟨h.mf⟩

/-- The converse: the lane's local binder is the general clause at `Type 0`.
The two are the same statement, so neither is stronger. -/
theorem input_of_amenableImpliesMF (h : CyclicBaseCalibration.AmenableImpliesMF) :
    QuasidiagonalMF.AmenableMFInput.{0} :=
  ⟨h.mf⟩

/-! ## The ledger's own claim, as a theorem -/

/-- **The aside is inert: the trust surface does not move.**

Three clauses in one type.  The paragraph's conclusion --- a homomorphism of
`E_BS` into the unitary group of a cofinite norm-matrix corona that does not
kill the marked word --- holds with no hypothesis; the aside's subject is
amenable, with no hypothesis; and the aside itself is a consequence of
`INT.11`.  The first clause is what the sharpness paragraph is for, and it
does not mention the third.

This is the formal content of proof-ledger row `CY.12c`'s note, which until now
was prose. -/
theorem aside_inert :
    (∃ X : ℕ → FiniteModel, (∀ n, 0 < Fintype.card (X n)) ∧
        ∃ Theta : LiteralGroup →* NormMatrixCoronaUnitary X, Theta mark ≠ 1) ∧
      Amenability.IsAmenable RealizedQuotient ∧
        (QuasidiagonalMF.AmenableMFInput.{0} → IsOperatorMF RealizedQuotient) :=
  ⟨CliffordQuotientMFUnconditional.exists_coronaRepresentation_mark_ne_one,
    realizedQuotient_isAmenable, isOperatorMF_realizedQuotient_of_input⟩

end CliffordAsideInert
end GroupApproximation
