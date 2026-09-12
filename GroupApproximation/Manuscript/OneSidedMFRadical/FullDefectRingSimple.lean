import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingCountable
import GroupApproximation.Manuscript.OneSidedMFRadical.FullDefectRingFullIdeal
import Mathlib.Algebra.CharP.Algebra

/-!
# `cor:simple-infinite-ring`

`non_mf_groups_exist.tex`, Corollary `cor:simple-infinite-ring`:

> If `R` is a countable simple unital ring that is not directly finite, then
> every homomorphism from `EL_n(R)` to an MF group is trivial for every
> `n ≥ 4`.  The same conclusion holds for `R = L_k(1,m)`, for every countable
> field `k` and every `m ≥ 2`.

Both cases are `thm:full-defect-ring` applied to a pair `s, t` produced here;
the two fullness verifications are `FullDefectRingFullIdeal`.

## "Directly finite", as printed and in Mathlib

The manuscript defines: "A unital ring is *directly finite* if `ts = 1` implies
`st = 1`."  That is Mathlib's `IsDedekindFiniteMonoid`, whose docstring records
the same three names for the condition ("von Neumann-finite or directly
finite"), so the printed hypothesis "not directly finite" is
`¬ IsDedekindFiniteMonoid R`, and `exists_oneSidedInverse_of_not_isDedekindFinite`
extracts the printed pair from it.

## What each corollary costs

The property-`(T)` input of `thm:full-defect-ring` is not automatic here: the
coefficient rings are arbitrary countable simple rings, and arbitrary countable
fields, so no characteristic hypothesis is available.  Each corollary therefore
appears twice.

* The general form carries `FinitelyGeneratedRingGeneralRankElementaryPropertyT`
  as a leading hypothesis, exactly as `thm:full-defect-ring` does.
* The prime-characteristic form carries no property-`(T)` hypothesis at all,
  because the Ershov--Jaikin-Zapirain theorem is proved in this repository over
  every finitely generated ring of prime characteristic.

For the Leavitt algebras the prime-characteristic form is the one over a
coefficient field of prime characteristic: `L_k(1,m)` is a `k`-algebra, and the
algebra map out of a field into a nontrivial ring is injective, so the
characteristic transports (`charP_of_injective_algebraMap`).

## Which Leavitt algebras

`Leavitt.AryLeavitt` presents `L_k(1,m)` for every field `k` and every `m` as
`AryLeavitt.AryLeavittAlgebra k m`, with its canonical `m`-ary family
`AryLeavitt.family k m : CompleteMatrixFamily _ (Fin m)`, so the printed range
`m ≥ 2` is covered exactly.  The printed choice `s = s₁`, `t = t₁`,
`t₂(1-s₁t₁)s₂ = 1` is `completeMatrixFamily_full` at the two indices `0` and
`1` of `Fin m`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

open scoped BigOperators

/-! ## The printed "not directly finite" hypothesis -/

/-- **A ring that is not directly finite has a one-sided inverse pair.**  The
printed definition "a unital ring is directly finite if `ts = 1` implies
`st = 1`" is `IsDedekindFiniteMonoid`, so its negation produces the pair
`ts = 1 ≠ st` that `thm:full-defect-ring` asks for. -/
theorem exists_oneSidedInverse_of_not_isDedekindFinite {R : Type*} [Ring R]
    (h : ¬ IsDedekindFiniteMonoid R) : ∃ s t : R, t * s = 1 ∧ s * t ≠ 1 := by
  by_contra hcon
  refine h ⟨fun {a b} hab ↦ ?_⟩
  by_contra hba
  exact hcon ⟨b, a, hab, hba⟩

/-! ## The simple case -/

/-- **`cor:simple-infinite-ring`, first sentence.**  For a countable simple
unital ring that is not directly finite, every homomorphism from `EL_n(R)` to
an MF group is trivial, for every `n ≥ 4`. -/
def PrintedSimpleInfiniteRing : Prop :=
  ∀ (R : Type) [Ring R] [Countable R] [IsSimpleRing R],
    ¬ IsDedekindFiniteMonoid R →
      ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M)
          (x : elementaryGroup (Fin n) R), f x = 1

/-- **The printed first case, proved.**  "Choose `ts = 1 ≠ st`; then `1 - st`
is a nonzero idempotent, and since `R` is simple it generates `R` as a
two-sided ideal", which is `isSimpleRing_full_of_not_directlyFinite`, and then
`thm:full-defect-ring` applies. -/
theorem manuscriptSimpleInfiniteRing
    (hfixed : FullDefectAtFixedRing)
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedSimpleInfiniteRing := by
  intro R _ _ _ hdf n hn M _ hM f x
  obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
  obtain ⟨hts', hfull⟩ := isSimpleRing_full_of_not_directlyFinite hts hst
  exact manuscriptFullComplementaryIdempotents hfixed hEJZ R s t hts' hfull n hn
    M hM f x

/-- **`cor:simple-infinite-ring` in prime characteristic**, with no
property-`(T)` hypothesis. -/
def PrintedSimpleInfiniteRingPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (R : Type) [Ring R] [Countable R] [CharP R p]
    [IsSimpleRing R], ¬ IsDedekindFiniteMonoid R →
      ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) R →* M)
          (x : elementaryGroup (Fin n) R), f x = 1

theorem manuscriptSimpleInfiniteRingPrimeChar
    (hfixed : FullDefectAtFixedRing) :
    PrintedSimpleInfiniteRingPrimeChar := by
  intro p hp R _ _ _ _ hdf n hn M _ hM f x
  obtain ⟨s, t, hts, hst⟩ := exists_oneSidedInverse_of_not_isDedekindFinite hdf
  obtain ⟨hts', hfull⟩ := isSimpleRing_full_of_not_directlyFinite hts hst
  exact manuscriptFullComplementaryIdempotentsPrimeChar hfixed p hp R s t hts'
    hfull n hn M hM f x

/-! ## The Leavitt case -/

section Leavitt

open AryLeavitt

/-- The two printed indices of the Leavitt case, `1` and `2` in the
manuscript's numbering, as elements of `Fin m` for `m ≥ 2`. -/
private theorem leavittIndices_ne {m : ℕ} (hm : 2 ≤ m) :
    (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ := by
  intro h
  exact absurd (congrArg Fin.val h) (by norm_num)

/-- The printed pair and its fullness in `L_k(1,m)`. -/
private theorem aryLeavitt_pair (k : Type) [Field k] (m : ℕ) (hm : 2 ≤ m) :
    (family k m).right ⟨0, by omega⟩ * (family k m).left ⟨0, by omega⟩ = 1 ∧
      ∃ (r : ℕ) (a b : Fin r → AryLeavittAlgebra k m),
        ∑ j, a j * (1 - (family k m).left ⟨0, by omega⟩ *
          (family k m).right ⟨0, by omega⟩) * b j = 1 :=
  completeMatrixFamily_full (family k m) (leavittIndices_ne hm)

/-- **`cor:simple-infinite-ring`, second sentence.**  For `R = L_k(1,m)` with
`k` a countable field and `m ≥ 2`, every homomorphism from `EL_n(R)` to an MF
group is trivial, for every `n ≥ 4`. -/
def PrintedLeavittAlgebraFullDefect : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (m : ℕ), 2 ≤ m →
    ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
      ∀ (f : elementaryGroup (Fin n) (AryLeavittAlgebra k m) →* M)
        (x : elementaryGroup (Fin n) (AryLeavittAlgebra k m)), f x = 1

/-- **The printed Leavitt case, proved.**  `s = s₁`, `t = t₁` and the single
sandwich `t₂(1-s₁t₁)s₂ = 1` are `completeMatrixFamily_full`; the rest is
`thm:full-defect-ring`. -/
theorem manuscriptLeavittAlgebraFullDefect
    (hfixed : FullDefectAtFixedRing)
    (hEJZ : FinitelyGeneratedRingGeneralRankElementaryPropertyT) :
    PrintedLeavittAlgebraFullDefect := by
  intro k _ _ m hm n hn M _ hM f x
  obtain ⟨hts, hfull⟩ := aryLeavitt_pair k m hm
  exact manuscriptFullComplementaryIdempotents hfixed hEJZ
    (AryLeavittAlgebra k m) _ _ hts hfull n hn M hM f x

/-- **The printed Leavitt case over a coefficient field of prime
characteristic**, with no property-`(T)` hypothesis.  `L_k(1,m)` is nontrivial
for `m ≥ 1`, so the algebra map out of the field is injective and the
characteristic transports. -/
def PrintedLeavittAlgebraFullDefectPrimeChar : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [Countable k] [CharP k p]
    (m : ℕ), 2 ≤ m →
      ∀ (n : ℕ), 4 ≤ n → ∀ (M : Type) [Group M], IsOperatorMF M →
        ∀ (f : elementaryGroup (Fin n) (AryLeavittAlgebra k m) →* M)
          (x : elementaryGroup (Fin n) (AryLeavittAlgebra k m)), f x = 1

theorem manuscriptLeavittAlgebraFullDefectPrimeChar
    (hfixed : FullDefectAtFixedRing) :
    PrintedLeavittAlgebraFullDefectPrimeChar := by
  intro p hp k _ _ _ m hm n hn M _ hM f x
  haveI : NeZero m := ⟨by omega⟩
  haveI : CharP (AryLeavittAlgebra k m) p :=
    charP_of_injective_algebraMap
      (algebraMap k (AryLeavittAlgebra k m)).injective p
  obtain ⟨hts, hfull⟩ := aryLeavitt_pair k m hm
  exact manuscriptFullComplementaryIdempotentsPrimeChar hfixed p hp
    (AryLeavittAlgebra k m) _ _ hts hfull n hn M hM f x

end Leavitt

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation
