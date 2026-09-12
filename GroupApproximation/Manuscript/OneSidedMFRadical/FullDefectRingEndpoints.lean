import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingSimple
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingMaximal
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring` and its corollaries: the printed clauses, one by one

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring`, the paragraph that
follows it, Corollary `cor:simple-infinite-ring` and Corollary
`cor:one-sided-ring-maximal`.

This module proves nothing new.  It is the inventory: one named proposition per
printed clause, each quoting the printed sentence in its docstring, so that a
reader can `#check` one name against one sentence of the manuscript.

## The clauses

| printed | proposition |
|---|---|
| `thm:full-defect-ring` | `PrintedFullComplementaryIdempotents` |
| "The hypothesis holds in every countable simple unital ring that is not directly finite and in every Leavitt algebra `L_k(1,m)`" | `PrintedFullnessHolds` |
| `cor:simple-infinite-ring`, first sentence | `PrintedSimpleInfiniteRing` |
| `cor:simple-infinite-ring`, second sentence | `PrintedLeavittAlgebraFullDefect` |
| `cor:one-sided-ring-maximal`, second sentence | `PrintedOneSidedRingMaximalReducedCStar` |

The first sentence of `cor:one-sided-ring-maximal` — "If a countable unital
ring `R` is not directly finite, then `C*_max(EL_n(R))` contains a proper
isometry for every `n ≥ 4`" — is a statement about the compressor rather than
about the MF radical: it needs the strict containment `uLu⁻¹ ⊊ L`, not the
saturation of the defect.  It is therefore not in this module.

## What is unconditional and what is not

`PrintedFullnessHolds` is unconditional and audited closed: it is the printed
verification that the hypothesis of `thm:full-defect-ring` is satisfiable, and
uses neither property `(T)` nor countability.

Every other clause carries two leading hypotheses, and both are open elsewhere
in the development rather than here.

* `FullDefectAtFixedRing` — the compression calculation of
  `thm:full-defect-ring` at a fixed ring, with its two property-`(T)` inputs
  named.  Its statement is in `FullDefectRingCountable`.
* `FinitelyGeneratedRingGeneralRankElementaryPropertyT` — the
  coefficient-general Ershov--Jaikin-Zapirain theorem, open in this repository
  in characteristic zero and at non-prime positive characteristic; see
  `PropertyT/EJZIntegralReduction`.

The second one disappears over coefficient rings of prime characteristic, which
is why every clause appears a second time in `...PrimeChar` form.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators
open AryLeavitt

/-! ## The satisfiability of the printed hypothesis -/

/-- **The sentence after `thm:full-defect-ring`, as one proposition.**

> The hypothesis holds in every countable simple unital ring that is not
> directly finite and in every Leavitt algebra `L_k(1,m)` over a countable
> field `k`, `m ≥ 2` (Corollary~`cor:simple-infinite-ring`).

Countability is what `thm:full-defect-ring` needs of the ring, not what the
hypothesis needs, so it is absent here: the two verifications below hold over
every simple ring that is not directly finite and over every field. -/
def PrintedFullnessHolds : Prop :=
  (∀ (R : Type) [Ring R] [IsSimpleRing R], ¬ IsDedekindFiniteMonoid R →
      ∃ s t : R, t * s = 1 ∧
        ∃ (m : ℕ) (a b : Fin m → R), ∑ k, a k * (1 - s * t) * b k = 1) ∧
    (∀ (k : Type) [Field k] (m : ℕ), 2 ≤ m →
      ∃ s t : AryLeavittAlgebra k m, t * s = 1 ∧
        ∃ (r : ℕ) (a b : Fin r → AryLeavittAlgebra k m),
          ∑ j, a j * (1 - s * t) * b j = 1)

/-- **The printed hypothesis is satisfiable, in both printed families.**
`isSimpleRing_full_of_not_directlyFinite` for the simple case,
`completeMatrixFamily_full` at the indices `0` and `1` of `Fin m` for
`L_k(1,m)`. -/
theorem manuscriptPrintedFullnessHolds : PrintedFullnessHolds := by
  constructor
  · intro R _ _ hdf
    obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
    exact ⟨s, t, isSimpleRing_full_of_not_directlyFinite hts hst⟩
  · intro k _ m hm
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    have hne : (⟨0, h0⟩ : Fin m) ≠ ⟨1, h1⟩ := by
      intro hcon
      exact absurd (congrArg Fin.val hcon) (by norm_num)
    exact ⟨(family k m).left ⟨0, h0⟩, (family k m).right ⟨0, h0⟩,
      completeMatrixFamily_full (family k m) hne⟩

/-! ## The whole printed programme, in its two forms -/

/-- **Every printed clause of `thm:full-defect-ring` and its corollaries that
depends on the compression calculation, as one proposition.**

In printed order: the theorem itself; the first sentence of
`cor:simple-infinite-ring`; its second sentence; and the second sentence of
`cor:one-sided-ring-maximal`. -/
def PrintedFullDefectRingProgramme : Prop :=
  PrintedFullComplementaryIdempotents ∧
    PrintedSimpleInfiniteRing ∧
    PrintedLeavittAlgebraFullDefect ∧
    PrintedOneSidedRingMaximalReducedCStar

/-- **The printed programme, from the two open inputs.**  Neither hypothesis is
a conjunct of the proposition: a proposition carrying its own hypothesis would
be a weaker statement wearing the printed theorem's name. -/
theorem manuscriptPrintedFullDefectRingProgramme
    (hfixed : FullDefectAtFixedRing)
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedFullDefectRingProgramme :=
  ⟨manuscriptFullComplementaryIdempotents hfixed hEJZ,
    manuscriptSimpleInfiniteRing hfixed hEJZ,
    manuscriptLeavittAlgebraFullDefect hfixed hEJZ,
    manuscriptOneSidedRingMaximalReducedCStar hfixed hEJZ⟩

/-- **The same four clauses over coefficient rings of prime characteristic**,
where the Ershov--Jaikin-Zapirain input is a theorem of this repository and no
property-`(T)` hypothesis survives.  For the Leavitt clause the hypothesis is
on the coefficient field, whose characteristic transports to `L_k(1,m)`. -/
def PrintedFullDefectRingProgrammePrimeChar : Prop :=
  PrintedFullComplementaryIdempotentsPrimeChar ∧
    PrintedSimpleInfiniteRingPrimeChar ∧
    PrintedLeavittAlgebraFullDefectPrimeChar ∧
    PrintedOneSidedRingMaximalReducedCStarPrimeChar

/-- **The prime-characteristic programme, from the compression calculation
alone.** -/
theorem manuscriptPrintedFullDefectRingProgrammePrimeChar
    (hfixed : FullDefectAtFixedRing) :
    PrintedFullDefectRingProgrammePrimeChar :=
  ⟨manuscriptFullComplementaryIdempotentsPrimeChar hfixed,
    manuscriptSimpleInfiniteRingPrimeChar hfixed,
    manuscriptLeavittAlgebraFullDefectPrimeChar hfixed,
    manuscriptOneSidedRingMaximalReducedCStarPrimeChar hfixed⟩

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.FullDefectRing.manuscriptPrintedFullnessHolds
