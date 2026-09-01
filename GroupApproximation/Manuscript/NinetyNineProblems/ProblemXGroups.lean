import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.ShulmanTraceNorms
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Sofic.ShulmanMFTraceBridge
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemX

/-!
# STW Problem X(1) at the canonical trace of a full group C⋆-algebra

Schafhauser, Tikuisis and White, *Nuclear C⋆-algebras: 99 problems*,
arXiv:2506.10902, print as Problem X(1):

> Is every amenable trace quasidiagonal?

`Manuscript.NinetyNineProblems.ProblemX` transcribes it as `ProblemX1Statement`,
quantified over every C⋆-algebra and every tracial state on it.  This module
restricts that quantifier to one family --- the canonical trace of the full
group C⋆-algebra `C⋆(G)` --- and reads off what the restriction says about
groups.

## What the restriction says

For a discrete group `G` the canonical trace of `C⋆(G)` is an amenable trace
exactly when `G` has Kirchberg's factorization property (Brown, *Invariant
means and finite representation theory of C⋆-algebras*, Mem. Amer. Math. Soc.
**184** (2006), no. 865, Theorem 4.1.9).  So at this family Problem X(1) reads:

> every group with the factorization property has a quasidiagonal canonical
> trace,

and a quasidiagonal canonical trace makes the group operator-MF.  The
composite, `amenableCanonicalTraceGroupsAreOperatorMF_of_problemX1`, is a
group-theoretic consequence of X(1): **the factorization property would imply
operator-MF**.  Read the other way,
`not_problemX1Statement_of_amenable_not_operatorMF` is the refutation shape ---
one group with the factorization property that is not operator-MF settles
Problem X(1) in the negative.

Neither the equivalence with the factorization property nor Brown's theorem is
formalized here.  This module speaks about the amenability of the canonical
trace, which is what `Quasidiagonal.IsAmenableTrace` transcribes and what the
repository can state; the factorization property enters only as the name Brown
gives that condition, in this docstring and in the docstrings below.

## The route, and why it is the maximal trace

`Analysis/TikuisisWhiteWinter.lean` already carries
`isOperatorMF_of_isQuasidiagonalCanonicalTrace`, but that theorem is about the
canonical faithful trace of the **reduced** algebra `C⋆_r(G)`, and it reaches
the maximal one by pulling back along `C⋆(G) → C⋆_r(G)`
(`ShulmanTrace.isMFTrace_canonicalMaximal_of_reducedTrace`).  Problem X(1) at
the factorization property is a statement about `C⋆(G)`, so the composite below
uses the maximal trace directly:

* `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` weakens the quasidiagonal
  models to Shulman's `MFTraceModel`, consuming the tracial-state datum
  (`ShulmanTrace.canonicalMaximalTracialState`, the canonical trace bundled)
  and the contractivity of unital completely positive matrix maps
  (`Quasidiagonal.ucpContractive`, a theorem, so no binder is left);
* `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` runs the corona
  argument of `Sofic/MFTraceCoronaBridge.lean`: shift away the finitely many
  empty models, take the corona homomorphism, correct it to a unitary
  representation, and read injectivity off the trace clause.

**No countability hypothesis appears.**  The corona route does not use one ---
unlike `ShulmanTrace.isOperatorMF_of_isMFTrace`, which reaches `IsOperatorMF`
through the local recognition argument and does carry `[Countable G]`.  The
theorems below are therefore stated without it; `Countable` is carried only
inside the named proposition, where it keeps the transcription inside Brown's
setting.

## Relation to the unconditional counterexample

The generic implications below retain Problem X(1) as a binder, but the
manuscript's group `E` now discharges the refutation hypotheses.
`ProblemX.literalFactorizationProperty` proves amenability of its canonical
trace from its locally-RF-by-`ℤ` decomposition, and `ProblemX.lean` combines
this with failure of quasidiagonality in the closed theorem
`ProblemX.not_problemX1Statement`.

The amenability hypothesis is not a consequence of soficity alone.  Thom
(Groups Geom. Dyn. **4** (2010),
195--208, arXiv:0810.2180) builds LEF --- so sofic, so hyperlinear --- Kazhdan
groups that are not residually finite, and by Kirchberg (Math. Ann. **299**
(1994), 551--563) a Kazhdan group with the factorization property is residually
finite.  So those groups are hyperlinear without the factorization property,
while `E` meets the hypothesis through its additional semidirect-product
structure.
-/

namespace GroupApproximation

namespace NinetyNineProblems

/-! ## Problem X(1) at the canonical trace, pointwise -/

/-- **A non-operator-MF group has a non-quasidiagonal canonical maximal
trace.**

Indeed, a quasidiagonal trace is an MF trace, and an MF canonical trace on the
full group C⋆-algebra makes the group operator-MF by the norm-matrix corona
argument.  No amenability or countability hypothesis is needed for this
obstruction. -/
theorem canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF
    (G : Type*) [Group G] (hnot : ¬ IsOperatorMF G) :
    ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  intro hqd
  apply hnot
  exact ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal
    (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace
      (IsTracialState.of_bundled (ShulmanTrace.canonicalMaximalTracialState G))
      Quasidiagonal.ucpContractive hqd)

def PrintedCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF : Prop :=
  ∀ (G : Type*) [Group G], ¬ IsOperatorMF G →
    ¬ Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

theorem manuscriptCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF :
    PrintedCanonicalMaximalTraceNotIsQuasidiagonalTraceOfNotIsOperatorMF := by
  intro G _ hnot
  exact canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF G hnot

/-- **The canonical maximal trace of an amenable-trace non-operator-MF group
is amenable and not quasidiagonal.**

This packages the two hypotheses in the exact trace-theoretic form used by
Problem X(1).  The failure of quasidiagonality is forced by `hnot`; it is not
an additional input. -/
theorem canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF :
    ∀ (G : Type*) [Group G],
      Quasidiagonal.IsAmenableTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
        (¬ IsOperatorMF G) →
          Quasidiagonal.IsAmenableTrace
              (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) ∧
            ¬ Quasidiagonal.IsQuasidiagonalTrace
              (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) := by
  intro G _ hamen hnot
  exact ⟨hamen,
    canonicalMaximalTrace_not_isQuasidiagonalTrace_of_not_isOperatorMF G hnot⟩

/-- **Problem X(1) makes a group with an amenable canonical trace
operator-MF.**

Two steps.  Problem X(1), applied at `C⋆(G)` and at the canonical trace bundled
as `ShulmanTrace.canonicalMaximalTracialState`, makes that trace quasidiagonal;
`Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` and
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` then carry it to
`IsOperatorMF G` through the norm-matrix corona.

The universe is pinned at `1` because `G : Type` and `MaximalGroupCStar` raises
the level by one, so `C⋆(G) : Type 1` --- the same pin `ProblemX.lean` uses.

By Brown's Theorem 4.1.9 the hypothesis is Kirchberg's factorization property
for `G`; see the module docstring for why that equivalence is named rather than
used. -/
theorem isOperatorMF_of_isAmenableCanonicalTrace_of_problemX1
    (hX : ProblemX1Statement.{1}) (G : Type) [Group G]
    (hamen : Quasidiagonal.IsAmenableTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)) :
    IsOperatorMF G := by
  have hqd : Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
    hX (MaximalGroupCStar G) (ShulmanTrace.canonicalMaximalTracialState G) hamen
  exact ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal
    (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace
      (IsTracialState.of_bundled (ShulmanTrace.canonicalMaximalTracialState G))
      Quasidiagonal.ucpContractive hqd)

/-! ## The group-theoretic consequence, as a proposition -/

/-- **The group-theoretic content of Problem X(1)**: every countable group
whose canonical trace on `C⋆(G)` is amenable is operator-MF.

By Brown, Mem. Amer. Math. Soc. **184** (2006), no. 865, Theorem 4.1.9, the
hypothesis is Kirchberg's factorization property, so this proposition says
*groups with the factorization property are MF*.  It is stated and not
asserted; `amenableCanonicalTraceGroupsAreOperatorMF_of_problemX1` derives it
from Problem X(1) and nothing else.

`Countable` is carried because Brown's theorem and the surrounding literature
are stated for countable discrete groups.  It is **not used**: the corona route
of `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` needs no
countability, so the pointwise theorem above omits it and is the stronger
statement.

Not to be confused with `QuasidiagonalMF.AmenableMFInput`, which asserts that
every countable **amenable group** is operator-MF.  An amenable group has the
factorization property, so the proposition here is the stronger clause --- but
that implication is standard rather than formalized, and neither proposition is
asserted anywhere in this repository. -/
def AmenableCanonicalTraceGroupsAreOperatorMF : Prop :=
  ∀ (G : Type) [Group G] [Countable G],
    Quasidiagonal.IsAmenableTrace
        (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
      IsOperatorMF G

/-- **Problem X(1) implies that groups with an amenable canonical trace are
operator-MF.**

The proposition is the pointwise theorem universally quantified, with the
unused countability hypothesis introduced and discarded. -/
theorem amenableCanonicalTraceGroupsAreOperatorMF_of_problemX1
    (hX : ProblemX1Statement.{1}) : AmenableCanonicalTraceGroupsAreOperatorMF := by
  intro G _instGroup _instCountable hamen
  exact isOperatorMF_of_isAmenableCanonicalTrace_of_problemX1 hX G hamen

/-! ## The refutation shape -/

/-- **One group with an amenable canonical trace that is not operator-MF
refutes Problem X(1).**

The contrapositive of the theorem above, stated where a reader looking for a
counterexample strategy will find it: by Brown's Theorem 4.1.9 the hypothesis
`hA` is Kirchberg's factorization property, so a *factorization-property
non-MF group* settles Problem X(1) in the negative.

Both hypotheses are about one group and neither mentions traces of other
algebras, which is the point of restricting the quantifier: X(1) ranges over
all C⋆-algebras, and a single group can still refute it.

The unconditional instance at the manuscript's own group is
`ProblemX.not_problemX1Statement`.  Its underlying conditional theorem,
`ProblemX.not_problemX1Statement_of_literalFactorizationProperty`, is the
literal-group specialization of the same amenable/non-quasidiagonal witness
shape. -/
theorem not_problemX1Statement_of_amenable_not_operatorMF :
    ∀ (G : Type) [Group G],
      Quasidiagonal.IsAmenableTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
        (¬ IsOperatorMF G) → ¬ ProblemX1Statement.{1} := by
  intro G _ hA hnot
  obtain ⟨hamen, hnotQD⟩ :=
    canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF
      G hA hnot
  intro hX
  exact hnotQD
    (hX (MaximalGroupCStar G) (ShulmanTrace.canonicalMaximalTracialState G) hamen)

end NinetyNineProblems

end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms canonicalMaximalTrace_amenable_not_isQuasidiagonalTrace_of_not_isOperatorMF
#audit_axioms not_problemX1Statement_of_amenable_not_operatorMF
