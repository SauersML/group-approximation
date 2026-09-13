import GroupApproximation.Pestov91.CrossedProduct
import GroupApproximation.PropertyT.FinitelyGeneratedRing

/-!
# `A ⋊ ℤ` is a finitely generated ring

The Ershov--Jaikin-Zapirain theorem (`Pestov91.elementary_hasKazhdanPropertyT`) asks only
`IsFinitelyGeneratedRing` of the coefficient ring.  For a crossed product this comes from one
observation: conjugation by the implementing unit is the action,
`u ^ j * C a * u ^ (-j) = C (ofAdd j • a)`.  So `u`, `u⁻¹`, and the images of finitely many
elements whose translates generate `A`, generate `A ⋊ ℤ`.

* `eq_top_of_unit_mem`: a subring containing `u`, `u⁻¹` and `C b` for `b ∈ s` is everything, when
  the translates of `s` generate `A` as a ring.
* `isFinitelyGeneratedRing_of_closure_translates`: `A ⋊ ℤ` is then finitely generated, by `u`,
  `u⁻¹` and `C '' s`.
* `isFinitelyGeneratedRing_of_adjoin_translates`: the same for an algebra over a finitely generated
  commutative ring `K`, when the translates of `s` generate `A` as a `K`-algebra.  For
  `A = LC(X, 𝔽_q)` over a subshift `X`, `s` is the set of coordinate-`0` cylinder indicators.
-/

namespace GroupApproximation
namespace Pestov91
namespace CrossedProduct

open Multiplicative (ofAdd)

/-- A subring of `A ⋊ ℤ` containing `u`, `u⁻¹` and `C b` for every `b ∈ s` is the whole ring, when
the translates of `s` generate `A` as a ring. -/
theorem eq_top_of_unit_mem {A : Type*} [Ring A] [MulSemiringAction (Multiplicative ℤ) A]
    {s : Set A} (hs : Subring.closure {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a} = ⊤)
    (S : Subring (SkewMonoidAlgebra A (Multiplicative ℤ)))
    (hu : ((unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) ∈ S)
    (hu' : ((unit⁻¹ : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) ∈ S)
    (hC : ∀ b ∈ s, C b ∈ S) : S = ⊤ := by
  have hpow : ∀ j : ℤ, ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) ∈ S := by
    intro j
    induction j using Int.induction_on with
    | zero => rw [zpow_zero, Units.val_one]; exact S.one_mem
    | succ i ih => rw [zpow_add_one, Units.val_mul]; exact S.mul_mem ih hu
    | pred i ih => rw [zpow_sub_one, Units.val_mul]; exact S.mul_mem ih hu'
  have htrans : {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a} ⊆ S.comap C := by
    rintro _ ⟨j, b, hb, rfl⟩
    rw [SetLike.mem_coe, Subring.mem_comap]
    have h : C (ofAdd j • b) = ((unit ^ j : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
        SkewMonoidAlgebra A (Multiplicative ℤ)) * C b *
        ((unit ^ (-j) : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
          SkewMonoidAlgebra A (Multiplicative ℤ)) := by
      rw [unit_zpow_mul_C, mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
        Units.val_one, mul_one]
    rw [h]
    exact S.mul_mem (S.mul_mem (hpow j) (hC b hb)) (hpow (-j))
  have hCall : ∀ a : A, C a ∈ S := fun a =>
    Subring.mem_comap.1 (Subring.closure_le.2 htrans ((Subring.eq_top_iff' _).1 hs a))
  refine (Subring.eq_top_iff' S).2 fun x => ?_
  obtain ⟨T, c, rfl⟩ := exists_sum_C_mul_unit_zpow x
  exact sum_mem fun j _ => S.mul_mem (hCall (c j)) (hpow j)

/-- **`A ⋊ ℤ` is a finitely generated ring** when the translates of a finite set `s ⊆ A` generate
`A` as a ring.  The generators are `u`, `u⁻¹` and `C b` for `b ∈ s`. -/
theorem isFinitelyGeneratedRing_of_closure_translates {A : Type*} [Ring A]
    [MulSemiringAction (Multiplicative ℤ) A] (s : Finset A)
    (hs : Subring.closure {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a} = ⊤) :
    IsFinitelyGeneratedRing (SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  classical
  refine ⟨insert ((unit : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ))
    (insert ((unit⁻¹ : (SkewMonoidAlgebra A (Multiplicative ℤ))ˣ) :
      SkewMonoidAlgebra A (Multiplicative ℤ)) (s.image C)), ?_⟩
  refine eq_top_of_unit_mem (s := (s : Set A)) hs _ ?_ ?_ ?_
  · exact Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  · exact Subring.subset_closure
      (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  · intro b hb
    exact Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem C (Finset.mem_coe.1 hb)))))

/-- **`A ⋊ ℤ` is a finitely generated ring** when `A` is an algebra over a finitely generated
commutative ring `K` and the translates of a finite set `s ⊆ A` generate `A` as a `K`-algebra. -/
theorem isFinitelyGeneratedRing_of_adjoin_translates {K A : Type*} [CommRing K] [Ring A]
    [Algebra K A] [MulSemiringAction (Multiplicative ℤ) A] (hK : IsFinitelyGeneratedRing K)
    (s : Finset A) (hs : Algebra.adjoin K {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a} = ⊤) :
    IsFinitelyGeneratedRing (SkewMonoidAlgebra A (Multiplicative ℤ)) := by
  classical
  obtain ⟨t, ht⟩ := hK
  refine isFinitelyGeneratedRing_of_closure_translates (s ∪ t.image (algebraMap K A)) ?_
  have hsub : {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a} ⊆
      {a : A | ∃ j : ℤ, ∃ b ∈ s ∪ t.image (algebraMap K A), ofAdd j • b = a} := by
    rintro _ ⟨j, b, hb, rfl⟩
    exact ⟨j, b, Finset.mem_union_left _ hb, rfl⟩
  have halg : ∀ k : K, algebraMap K A k ∈
      Subring.closure {a : A | ∃ j : ℤ, ∃ b ∈ s ∪ t.image (algebraMap K A), ofAdd j • b = a} := by
    intro k
    have hle : Subring.closure (t : Set K) ≤
        (Subring.closure {a : A | ∃ j : ℤ, ∃ b ∈ s ∪ t.image (algebraMap K A),
          ofAdd j • b = a}).comap (algebraMap K A) := by
      refine Subring.closure_le.2 fun k' hk' => ?_
      rw [SetLike.mem_coe, Subring.mem_comap]
      exact Subring.subset_closure ⟨0, algebraMap K A k', Finset.mem_union_right _
        (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hk')), by rw [ofAdd_zero, one_smul]⟩
    exact Subring.mem_comap.1 (hle ((Subring.eq_top_iff' _).1 ht k))
  have hle : Subring.closure
      (Set.range (algebraMap K A) ∪ {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a}) ≤
      Subring.closure {a : A | ∃ j : ℤ, ∃ b ∈ s ∪ t.image (algebraMap K A), ofAdd j • b = a} := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨k, rfl⟩ | hx)
    · exact halg k
    · exact Subring.subset_closure (hsub hx)
  refine (Subring.eq_top_iff' _).2 fun a => ?_
  have ha : a ∈ (Algebra.adjoin K {a : A | ∃ j : ℤ, ∃ b ∈ s, ofAdd j • b = a}).toSubring := by
    rw [hs]; exact Subalgebra.mem_toSubring.2 Algebra.mem_top
  rw [Algebra.adjoin_eq_ring_closure] at ha
  exact hle ha

end CrossedProduct
end Pestov91
end GroupApproximation
