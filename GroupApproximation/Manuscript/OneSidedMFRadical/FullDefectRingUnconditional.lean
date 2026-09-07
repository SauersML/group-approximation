import GroupApproximation.Leavitt.FullDefectRingAtFixedRing
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingEndpoints
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring` and its corollaries with the ring calculation spent

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`, Corollary
`cor:simple-infinite-ring`, Corollary `cor:one-sided-ring-maximal`.

Every printed clause of these three statements was proved with two leading
hypotheses, `FullDefectAtFixedRing` and
`FinitelyGeneratedRingGeneralRankElementaryPropertyT`.  The first is now a
theorem — `Leavitt/FullDefectRingAtFixedRing`'s `fullDefectAtFixedRing`, the
seam between the rank-`n` compressor calculation and the compression criterion
— so this module spends it once and for all, and states each printed clause in
the two forms that remain.

* **Prime characteristic: nothing is assumed.**  The
  Ershov--Jaikin-Zapirain theorem is proved in this repository over every
  finitely generated ring of prime characteristic, so over such coefficient
  rings each clause is a hypothesis-free theorem.  These are the declarations
  carrying `#audit_closed_axioms` below.
* **General characteristic: one hypothesis.**  Everything else keeps exactly
  one leading hypothesis, the coefficient-general Ershov--Jaikin-Zapirain
  statement, which `PropertyT/EJZIntegralReduction` reduces to the integral
  free case and which is open in this repository in characteristic zero and at
  non-prime positive characteristic.

Almost nothing is proved here.  Each declaration is an existing theorem of this
lane with its first argument supplied, and the reason to name the results is
that a badge should point at a declaration whose elaborated type is the printed
sentence and nothing else.  The one exception is the group-level failure of
MF-ness at the end, which had no name of its own: `thm:full-defect-ring` is
stated as the triviality of every homomorphism to an MF group, and "so
`EL_n(R)` is not MF" is the reading a reader draws from it, by taking the
target to be `EL_n(R)` itself.

The one printed clause still carrying a different hypothesis is the first
sentence of `cor:one-sided-ring-maximal`, the proper isometry in
`C*_max(EL_n(R))`; its input is `OneSidedCompressorStrictContainment`, the
strictness of the compression, which is not a consequence of
`thm:full-defect-ring` and is tracked in `FullDefectRingProperIsometry`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

/-! ## Prime characteristic: the printed clauses, hypothesis-free -/

/-- **`thm:full-defect-ring` over a coefficient ring of prime characteristic,
with no hypothesis.**

> Let `R` be a countable unital associative ring.  Suppose that `s,t ∈ R`
> satisfy `ts = 1`, `R(1-st)R = R`.  For every `n ≥ 4`, every homomorphism from
> `EL_n(R)` to an MF group is trivial. -/
theorem manuscriptFullComplementaryIdempotentsPrimeCharUnconditional :
    PrintedFullComplementaryIdempotentsPrimeChar :=
  manuscriptFullComplementaryIdempotentsPrimeChar fullDefectAtFixedRing

/-- **`cor:simple-infinite-ring`, first sentence, in prime characteristic.**

> If `R` is a countable simple unital ring that is not directly finite, then
> every homomorphism from `EL_n(R)` to an MF group is trivial for every
> `n ≥ 4`. -/
theorem manuscriptSimpleInfiniteRingPrimeCharUnconditional :
    PrintedSimpleInfiniteRingPrimeChar :=
  manuscriptSimpleInfiniteRingPrimeChar fullDefectAtFixedRing

/-- **`cor:simple-infinite-ring`, second sentence, over a coefficient field of
prime characteristic.**

> The same conclusion holds for `R = L_k(1,m)`, for every countable field `k`
> and every `m ≥ 2`. -/
theorem manuscriptLeavittAlgebraFullDefectPrimeCharUnconditional :
    PrintedLeavittAlgebraFullDefectPrimeChar :=
  manuscriptLeavittAlgebraFullDefectPrimeChar fullDefectAtFixedRing

/-- **`cor:one-sided-ring-maximal`, second sentence, in prime
characteristic.**

> If `R ≠ 0` also satisfies the hypothesis of Theorem `thm:full-defect-ring`,
> then `C*_r(EL_n(R))` is separable, stably finite, and not MF. -/
theorem manuscriptOneSidedRingMaximalReducedCStarPrimeCharUnconditional :
    PrintedOneSidedRingMaximalReducedCStarPrimeChar :=
  manuscriptOneSidedRingMaximalReducedCStarPrimeChar fullDefectAtFixedRing

/-- **All four clauses at once, in prime characteristic, hypothesis-free.** -/
theorem manuscriptPrintedFullDefectRingProgrammePrimeCharUnconditional :
    PrintedFullDefectRingProgrammePrimeChar :=
  manuscriptPrintedFullDefectRingProgrammePrimeChar fullDefectAtFixedRing

/-! ## General characteristic: one hypothesis, the printed citation -/

/-- **`thm:full-defect-ring` exactly as printed**, with the
Ershov--Jaikin-Zapirain theorem as its only hypothesis. -/
theorem manuscriptFullComplementaryIdempotentsFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedFullComplementaryIdempotents :=
  manuscriptFullComplementaryIdempotents fullDefectAtFixedRing hEJZ

/-- **`cor:simple-infinite-ring`, first sentence, as printed.** -/
theorem manuscriptSimpleInfiniteRingFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedSimpleInfiniteRing :=
  manuscriptSimpleInfiniteRing fullDefectAtFixedRing hEJZ

/-- **`cor:simple-infinite-ring`, second sentence, as printed.** -/
theorem manuscriptLeavittAlgebraFullDefectFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedLeavittAlgebraFullDefect :=
  manuscriptLeavittAlgebraFullDefect fullDefectAtFixedRing hEJZ

/-- **`cor:one-sided-ring-maximal`, second sentence, as printed.** -/
theorem manuscriptOneSidedRingMaximalReducedCStarFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedOneSidedRingMaximalReducedCStar :=
  manuscriptOneSidedRingMaximalReducedCStar fullDefectAtFixedRing hEJZ

/-- **All four clauses at once, as printed.** -/
theorem manuscriptPrintedFullDefectRingProgrammeFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedFullDefectRingProgramme :=
  manuscriptPrintedFullDefectRingProgramme fullDefectAtFixedRing hEJZ

/-! ## The group-level reading: `EL_n(R)` is not MF -/

/-- **`EL_n(R)` is itself not MF.**

`thm:full-defect-ring` is printed as the triviality of every homomorphism from
`EL_n(R)` to an MF group.  The reading the manuscript draws from it — the one
that makes `EL_n(R)` an example rather than an obstruction theorem — is that
the group is not MF, and that is this proposition.

It is a one-line consequence, and the line is where `R ≠ 0` is spent: if
`EL_n(R)` were MF then the identity homomorphism would be a homomorphism to an
MF group, so every element would be trivial, and `EL_n(R)` is not trivial
because `R` is not.

The countability instance is supplied inside the statement, because
`IsCDEOperatorMF` asks for it and `EL_n(R)` carries it only through
`countable_elementaryGroup`. -/
def PrintedElementaryGroupNotMFPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R]
    [CharP R p] (s t : R), t * s = 1 →
      (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
        ∀ (n : ℕ), 4 ≤ n →
          letI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
          ¬ IsCDEOperatorMF (elementaryGroup (Fin n) R)

/-- **`EL_n(R)` is not MF, over a coefficient ring of prime characteristic, with
no hypothesis.** -/
theorem manuscriptElementaryGroupNotMFPrimeChar :
    PrintedElementaryGroupNotMFPrimeChar := by
  intro p hp R _ _ _ _ s t hts hfull n hn
  haveI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    nontrivial_elementaryGroup (R := R) hne
  exact not_isCDEOperatorMF_of_killsMFTargets fun M _ hM f x ↦
    manuscriptFullComplementaryIdempotentsPrimeCharUnconditional p hp R s t hts
      hfull n hn M hM f x

/-- **`EL_n(R)` is not MF, as printed**, with the Ershov--Jaikin-Zapirain
theorem as its only hypothesis. -/
def PrintedElementaryGroupNotMF : Prop :=
  ∀ (R : Type) [Ring R] [Nontrivial R] [Countable R] (s t : R), t * s = 1 →
    (∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) →
      ∀ (n : ℕ), 4 ≤ n →
        letI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
        ¬ IsCDEOperatorMF (elementaryGroup (Fin n) R)

theorem manuscriptElementaryGroupNotMFFromEJZ
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedElementaryGroupNotMF := by
  intro R _ _ _ s t hts hfull n hn
  haveI : Countable (elementaryGroup (Fin n) R) := countable_elementaryGroup
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  haveI : Nontrivial (elementaryGroup (Fin n) R) :=
    nontrivial_elementaryGroup (R := R) hne
  exact not_isCDEOperatorMF_of_killsMFTargets fun M _ hM f x ↦
    manuscriptFullComplementaryIdempotentsFromEJZ hEJZ R s t hts hfull n hn M hM
      f x

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation
open GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRing

#audit_closed_axioms
  manuscriptFullComplementaryIdempotentsPrimeCharUnconditional
#audit_closed_axioms manuscriptSimpleInfiniteRingPrimeCharUnconditional
#audit_closed_axioms manuscriptLeavittAlgebraFullDefectPrimeCharUnconditional
#audit_closed_axioms
  manuscriptOneSidedRingMaximalReducedCStarPrimeCharUnconditional
#audit_closed_axioms
  manuscriptPrintedFullDefectRingProgrammePrimeCharUnconditional
#audit_closed_axioms manuscriptElementaryGroupNotMFPrimeChar
