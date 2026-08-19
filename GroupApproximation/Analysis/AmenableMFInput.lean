import GroupApproximation.Analysis.PropertyTNonamenable
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.OperatorMFPositiveControls

/-!
# `INT.11`: "all amenable groups are MF, by quasidiagonality", as a typed input

`non_mf_groups_exist.tex`, the introduction (grep `"quasidiagonality \cite{TWW}"`,
never a line number --- the file is edited concurrently).  Proof-ledger row
`INT.11` grades that clause `MISSING`/`literature-input`: it is the
Tikuisis--White--Winter theorem, it is formalized in no proof assistant, and
under the zero-literature order a citation route would not close it either.

This module does not close the row and cannot.  What it does is give the
sentence a *type*, and then prove everything about that type which is a
theorem rather than a citation.  Three things are established.

## 1.  The sentence has a name, and it is universe-polymorphic

`AmenableMFInput.{u}` is the printed clause verbatim: every countable amenable
group of `Type u` is operator-MF.  **No inhabitant is constructed anywhere in
this repository, and none is postulated.**  Until now the clause existed
in-tree only twice, both times pinned to `Type 0` and both times inside the
Clifford lane --- as `CyclicBaseCalibration.AmenableImpliesMF` and as an inline
binder in `Sofic.CliffordBSPrintedRoute`.  `INT.11` is an *introduction* row and
its second use site (`\label{sec:consequences}`, grep
`"homomorphism to any countable"`) quantifies over all countable amenable
groups, so the general form belongs outside that lane.  `Sofic.CliffordAsideInert`
proves the general form implies the lane's local one.

## 2.  The words "by quasidiagonality" name a factorization, and the
factorization is a theorem

The printed clause does not assert a bare implication; it asserts a *route*.
`amenableMFInput_of_quasidiagonalRoute` is that route, stated for an arbitrary
intermediate predicate `QD`: whoever supplies

* amenable countable groups satisfy `QD` --- Tikuisis--White--Winter proper, and
* countable groups satisfying `QD` are operator-MF --- the elementary reduction,

supplies `AmenableMFInput`.  The composition step is proved here; neither
premise is.  The two halves are of genuinely different difficulty, which is why
separating them is worth doing: `Analysis.QuasidiagonalCompression` already
proves the analytic core of the *second* premise (compressions by an
asymptotically commuting sequence of finite-rank projections are asymptotically
multiplicative, converge strongly, and separate points against a faithful
representation), and what is missing there is matrix-coordinate bookkeeping
against the corona's conventions.  The *first* premise is the theorem.  A
reader who wants to know how much of `INT.11` is out of reach should read this
factorization: the answer is "one of the two premises, and it is the hard one".

## 3.  The input is consistent with the manuscript's own theorems, and this is
proved rather than asserted

The manuscript produces groups that are **not** operator-MF.  An auditor's
first question is whether that refutes the input it cites in its own
introduction.  It does not, and the reason is unconditional:
`not_isAmenable_of_infinite_kazhdanComplex` --- every infinite Kazhdan group
fails to be amenable, proved outright in `Analysis.PropertyTNonamenable` --- so
at every group the manuscript constructs, the input's hypothesis is false and
the input says nothing.  `input_says_nothing_at_infinite_kazhdan` records
exactly that, and it takes the input as a hypothesis only to discard it.

## What is reachable without the input

`amenableMF_of_isLEF`, `amenableMF_of_locallyFinite` and
`amenableMF_of_residuallyFinite` are the three classes where the printed
conclusion is already machine-checked, and all three factor through *exact*
finite models.  `Algebra.AmenableMFProof` proves that the Følner construction
--- the only elementary route to MF for an amenable group --- cannot leave that
class: permutation operator-norm defects are `0` or at least `1`, so
permutation models certify exactly the LEF groups.  So the gap between what is
proved here and what `INT.11` prints is not slack in the estimates; it is the
whole of Tikuisis--White--Winter.
-/

namespace GroupApproximation
namespace QuasidiagonalMF

universe u w

/-! ## The input -/

/-- **`INT.11`, as a typed input.**  Every countable amenable group is
operator-MF: the Tikuisis--White--Winter theorem, which the manuscript's
introduction cites and which this development does not prove.

**No inhabitant of this structure is constructed anywhere in this repository,
and none can be without formalizing that theorem.**  It is a structure rather
than an axiom precisely so that consuming it leaves a visible binder in the
type of every theorem that does. -/
structure AmenableMFInput : Prop where
  /-- Countable amenable groups are operator-MF. -/
  mf : ∀ (G : Type u) [Group G] [Countable G],
    Amenability.IsAmenable G → IsOperatorMF G

/-! ## The words "by quasidiagonality"

The printed clause names a route through quasidiagonality rather than a bare
implication.  Stated at an arbitrary intermediate predicate, that route is a
theorem: what is not proved is either of its two premises. -/

/-- **The factorization the printed clause names.**  Any predicate `QD` that
holds of countable amenable groups and implies operator-MF for countable groups
gives the printed conclusion, group by group.  Taking `QD` to be
quasidiagonality of the reduced group `C*`-algebra makes the first premise
Tikuisis--White--Winter and the second the elementary reduction whose analytic
core is `Analysis.QuasidiagonalCompression`.

Neither premise is discharged here.  The content of this theorem is that the
*only* thing joining them is composition --- there is no third step hiding in
the word "by".

**Why this is stated group by group rather than as a producer of
`AmenableMFInput`.**  The two premises are bare `∀`-formulas, and
`scripts/check_non_mf_unconditional.py` judges such a premise by the head
symbols it mentions rather than by whether it is provable --- a blind spot its
own docstring records.  A declaration concluding `AmenableMFInput` from them
would therefore enter that checker's discharge fixpoint as a *producer* of the
input with no undischarged requirement, and the input would silently stop being
reported as open.  It is not inhabited, so it must not be reported as
inhabited.  Universally quantifying the conclusion below recovers
`AmenableMFInput` in one step for any reader who wants it, and asserts
nothing. -/
theorem isOperatorMF_of_quasidiagonalRoute
    (QD : ∀ (G : Type u) [Group G], Prop)
    (amenable_qd : ∀ (G : Type u) [Group G] [Countable G],
      Amenability.IsAmenable G → QD G)
    (qd_mf : ∀ (G : Type u) [Group G] [Countable G],
      QD G → IsOperatorMF G)
    (G : Type u) [Group G] [Countable G] (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  qd_mf G (amenable_qd G hA)

/-! ## Consequences of the input, as theorems about the binder -/

variable {G : Type u} [Group G]

/-- **The contrapositive.**  Granting the input, a countable group that is not
operator-MF is not amenable.  This is the shape in which the manuscript's
`\label{sec:consequences}` paragraph uses the clause. -/
theorem AmenableMFInput.not_isAmenable_of_not_isOperatorMF
    (h : AmenableMFInput.{u}) [Countable G] (hMF : ¬ IsOperatorMF G) :
    ¬ Amenability.IsAmenable G :=
  fun hA ↦ hMF (h.mf G hA)

/-! ## The input is consistent with the manuscript's own theorems -/

/-- **Every infinite Kazhdan group is nonamenable**, with no input at all.
Restated from `Analysis.PropertyTNonamenable`, where it is proved from Følner
sets and the absence of invariant vectors in the regular representation. -/
theorem not_isAmenable_of_infinite_kazhdanComplex [Infinite G]
    (hT : HasKazhdanPropertyTComplex.{u, max u w} G) :
    ¬ Amenability.IsAmenable G :=
  PropertyTNonamenable.infinite_kazhdanTextbook_not_isAmenable hT

/-- **The input says nothing at the groups the manuscript constructs, and
therefore cannot be refuted by them.**

Every group produced by the Kazhdan--Clifford construction is infinite and has
property `(T)`, so the input's hypothesis --- amenability --- already fails,
unconditionally.  The input is taken as a hypothesis here only so that the
statement is about it; the conclusion does not use it, which is the whole
point.  Theorem A of the manuscript exhibits a group that is not operator-MF,
and this is why that is not a counterexample to the clause its own
introduction cites. -/
theorem input_says_nothing_at_infinite_kazhdan (_h : AmenableMFInput.{u})
    [Infinite G] (hT : HasKazhdanPropertyTComplex.{u, max u w} G) :
    ¬ Amenability.IsAmenable G :=
  not_isAmenable_of_infinite_kazhdanComplex hT

/-! ## What is reachable without the input

The printed conclusion is machine-checked on three classes.  All three factor
through exact finite models, and `Algebra.AmenableMFProof` proves that the
Følner construction cannot leave that class, so these are not partial progress
towards the input --- they are its complement. -/

/-- Countable LEF groups are operator-MF, amenable or not. -/
theorem amenableMF_of_isLEF [Countable G] (_hA : Amenability.IsAmenable G)
    (hLEF : IsLEF G) : IsOperatorMF G :=
  isOperatorMF_of_isLEF hLEF

/-- Countable locally finite groups --- amenable, and MF outright. -/
theorem amenableMF_of_locallyFinite [Countable G]
    (hG : IsLocallyFiniteGroup G) : IsOperatorMF G :=
  isOperatorMF_of_locallyFinite hG

/-- Countable residually finite groups are operator-MF; in particular the
input adds nothing at a residually finite amenable group. -/
theorem amenableMF_of_residuallyFinite [Countable G]
    [Group.ResiduallyFinite G] (_hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_residuallyFinite

end QuasidiagonalMF
end GroupApproximation
