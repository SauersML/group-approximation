import GroupApproximation.Analysis.PolarLiftingGeneralCStar
import GroupApproximation.Analysis.CStarIdealApproximateUnit

/-!
# The reduced product of arbitrary C-star algebras as a C-star algebra

`Analysis/PolarLiftingGeneralCStar` constructs the algebraic reduced product

`(prod_n A_n) / (direct sum_n A_n)`

and its involution, but deliberately does not put the quotient norm on it.
The general quotient theorem in `Analysis/CStarIdealApproximateUnit` now makes
that omission unnecessary.  This file proves that the null-sequence ideal is
closed and packages its star stability; the general theorem then supplies the
genuine quotient C-star structure.

This is the ambient object needed by the reduced-product permanence lemma for
MF algebras.  No matrix-block hypothesis occurs here.
-/

namespace GroupApproximation
namespace PolarLiftingGeneralCStar

open Filter

noncomputable section

universe u

variable (A : ℕ → Type u) [∀ n, CStarAlgebra (A n)]
  [∀ n, Nontrivial (A n)] (l : Filter ℕ)

/-- The bounded dependent product has all six parent structures of a unital
complex C-star algebra coordinatewise.  Mathlib exposes those parents on
`lp A ∞` but does not assemble the noncommutative bundled class. -/
noncomputable instance boundedCStarSequenceCStarAlgebra :
    CStarAlgebra (BoundedCStarSequence A) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- The bounded product is nontrivial because every coordinate algebra is.
This explicit assembly is needed by the general closed-ideal quotient theorem;
the parent `lp` API exposes the instance only after its subtype is unfolded. -/
noncomputable instance boundedCStarSequenceNontrivial :
    Nontrivial (BoundedCStarSequence A) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have hcoord := congrArg (fun x : BoundedCStarSequence A ↦ x 0) h
  exact zero_ne_one hcoord

private theorem boundedCStarSequence_coord_dist_le
    (a b : BoundedCStarSequence A) (n : ℕ) :
    dist (a n) (b n) ≤ dist a b := by
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(a - b) n‖ ≤ ‖a - b‖
  exact boundedCStarSequence_coord_norm_le A (a - b) n

/-- The `l`-null sequences form a closed ideal of the bounded product. -/
theorem isClosed_nullCStarSequenceIdeal :
    IsClosed (nullCStarSequenceIdeal A l : Set (BoundedCStarSequence A)) := by
  apply IsSeqClosed.isClosed
  intro s a hs hsa
  change IsNullCStarSequence A l a
  rw [IsNullCStarSequence, Metric.tendsto_nhds]
  intro ε hε
  have hclose : ∀ᶠ k in atTop, dist (s k) a < ε / 2 :=
    (Metric.tendsto_nhds.mp hsa) (ε / 2) (half_pos hε)
  obtain ⟨k, hk⟩ := hclose.exists
  have hsk : IsNullCStarSequence A l (s k) := hs k
  have htail : ∀ᶠ n in l, ‖s k n‖ < ε / 2 :=
    (Metric.tendsto_nhds.mp hsk) (ε / 2) (half_pos hε) |>.mono fun n hn ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_norm] using hn
  filter_upwards [htail] with n hn
  rw [Real.dist_eq, sub_zero, abs_norm]
  calc
    ‖a n‖ ≤ ‖a n - s k n‖ + ‖s k n‖ := by
      nth_rewrite 1 [← sub_add_cancel (a n) (s k n)]
      exact norm_add_le _ _
    _ < ε := by
      have hcoord : ‖a n - s k n‖ < ε / 2 := by
        calc
          ‖a n - s k n‖ = dist (a n) (s k n) := by rw [dist_eq_norm]
          _ ≤ dist a (s k) := boundedCStarSequence_coord_dist_le A a (s k) n
          _ = dist (s k) a := dist_comm _ _
          _ < ε / 2 := hk
      linarith

noncomputable instance nullCStarSequenceIdeal_isClosed :
    IsClosed (nullCStarSequenceIdeal A l : Set (BoundedCStarSequence A)) :=
  isClosed_nullCStarSequenceIdeal A l

noncomputable instance nullCStarSequenceIdeal_isStarStable :
    CStarTensor.IsStarStable (nullCStarSequenceIdeal A l) where
  star_mem := nullCStarSequenceIdeal_star_mem A l

/-- Audit pin: after closedness and star stability are installed, the general
closed-ideal quotient theorem gives the reduced product its genuine bundled
C-star-algebra structure. -/
theorem cStarProductCorona_hasCStarAlgebra :
    Nonempty (CStarAlgebra (CStarProductCorona A l)) :=
  ⟨inferInstance⟩

/-- The quotient map from the bounded product to the reduced product, as a
complex star-algebra homomorphism. -/
noncomputable def cStarProductCoronaQuotient :
    BoundedCStarSequence A →⋆ₐ[ℂ] CStarProductCorona A l :=
  CStarTensor.quotientStarMk (nullCStarSequenceIdeal A l)

@[simp] theorem cStarProductCoronaQuotient_apply
    (a : BoundedCStarSequence A) :
    cStarProductCoronaQuotient A l a =
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a := rfl

/-- A bounded sequence represents zero exactly when it is null along the
defining filter. -/
theorem cStarProductCoronaQuotient_eq_zero_iff
    (a : BoundedCStarSequence A) :
    cStarProductCoronaQuotient A l a = 0 ↔ IsNullCStarSequence A l a := by
  rw [cStarProductCoronaQuotient_apply, Ideal.Quotient.eq_zero_iff_mem]
  rfl

/-- Every reduced-product class has a bounded representative. -/
theorem cStarProductCoronaQuotient_surjective :
    Function.Surjective (cStarProductCoronaQuotient A l) :=
  Ideal.Quotient.mk_surjective

/-! ## The printed quotient norm formula -/

open scoped Classical in
/-- Restrict a bounded sequence to a set of coordinates, extending it by
zero off that set. -/
private def boundedCStarSequenceOn (a : BoundedCStarSequence A) (S : Set ℕ) :
    BoundedCStarSequence A :=
  ⟨fun n ↦ if n ∈ S then a n else 0,
    (lp.memℓp a).mono' fun n ↦ by
      split_ifs
      · exact le_rfl
      · simp⟩

omit [∀ n, Nontrivial (A n)] in
open scoped Classical in
@[simp] private theorem boundedCStarSequenceOn_apply
    (a : BoundedCStarSequence A) (S : Set ℕ) (n : ℕ) :
    boundedCStarSequenceOn A a S n = if n ∈ S then a n else 0 := rfl

omit [∀ n, Nontrivial (A n)] in
private theorem boundedCStarSequence_sub_on_isNull
    (a : BoundedCStarSequence A) {S : Set ℕ} (hS : S ∈ l) :
    IsNullCStarSequence A l (a - boundedCStarSequenceOn A a S) := by
  rw [IsNullCStarSequence]
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [hS] with n hn
  simp [boundedCStarSequenceOn_apply, hn]

omit [∀ n, Nontrivial (A n)] in
private theorem norm_boundedCStarSequenceOn_le (a : BoundedCStarSequence A)
    {S : Set ℕ} {c : ℝ} (hc : 0 ≤ c) (hS : ∀ n ∈ S, ‖a n‖ ≤ c) :
    ‖boundedCStarSequenceOn A a S‖ ≤ c := by
  rw [lp.norm_eq_ciSup]
  apply ciSup_le
  intro n
  simp only [boundedCStarSequenceOn_apply]
  split_ifs with hn
  · exact hS n hn
  · simpa using hc

private theorem cStarProductCorona_norm_mk_le (a : BoundedCStarSequence A) :
    ‖Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a‖ ≤ ‖a‖ :=
  Submodule.Quotient.norm_mk_le (nullCStarSequenceIdeal A l) a

private def cStarSequenceFilterNorm (a : BoundedCStarSequence A) : ℝ :=
  Filter.limsup (fun n ↦ ‖a n‖) l

omit [∀ n, Nontrivial (A n)] in
private theorem cStarNorm_isBoundedUnder (a : BoundedCStarSequence A) :
    IsBoundedUnder (· ≤ ·) l (fun n : ℕ ↦ ‖a n‖) :=
  ⟨‖a‖, show ∀ᶠ n : ℕ in l, ‖a n‖ ≤ ‖a‖ from
    Eventually.of_forall fun n ↦ boundedCStarSequence_coord_norm_le A a n⟩

omit [∀ n, Nontrivial (A n)] in
private theorem cStarNorm_isCoboundedUnder [l.NeBot]
    (a : BoundedCStarSequence A) :
    IsCoboundedUnder (· ≤ ·) l (fun n : ℕ ↦ ‖a n‖) :=
  Filter.isCoboundedUnder_le_of_le l fun n ↦ norm_nonneg (a n)

omit [∀ n, Nontrivial (A n)] in
private theorem cStarSequenceFilterNorm_nonneg [l.NeBot]
    (a : BoundedCStarSequence A) : 0 ≤ cStarSequenceFilterNorm A l a := by
  apply (Filter.le_limsup_iff
    (cStarNorm_isCoboundedUnder A l a) (cStarNorm_isBoundedUnder A l a)).mpr
  intro y hy
  exact Frequently.of_forall fun n ↦ hy.trans_le (norm_nonneg (a n))

private theorem cStarProductCorona_mk_le_filterNorm [l.NeBot]
    (a : BoundedCStarSequence A) :
    ‖Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a‖ ≤
      cStarSequenceFilterNorm A l a := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ n in l, ‖a n‖ < cStarSequenceFilterNorm A l a + ε :=
    Filter.eventually_lt_of_limsup_lt (lt_add_of_pos_right _ hε)
      (cStarNorm_isBoundedUnder A l a)
  have hS : {n : ℕ | ‖a n‖ < cStarSequenceFilterNorm A l a + ε} ∈ l := hev
  have hquot : Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a =
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l)
        (boundedCStarSequenceOn A a
          {n : ℕ | ‖a n‖ < cStarSequenceFilterNorm A l a + ε}) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact boundedCStarSequence_sub_on_isNull A l a hS
  rw [hquot]
  exact (cStarProductCorona_norm_mk_le A l _).trans
    (norm_boundedCStarSequenceOn_le A a
      (add_nonneg (cStarSequenceFilterNorm_nonneg A l a) hε.le)
      fun n hn ↦ le_of_lt hn)

omit [∀ n, Nontrivial (A n)] in
private theorem eventually_norm_sub_lt_of_isNull
    (a b : BoundedCStarSequence A)
    (hab : IsNullCStarSequence A l (a - b)) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n in l, ‖(a - b) n‖ < c :=
  (Metric.tendsto_nhds.mp hab) c hc |>.mono fun n hn ↦ by
    simpa only [Real.dist_eq, sub_zero, abs_norm] using hn

omit [∀ n, Nontrivial (A n)] in
private theorem cStarNorm_le_norm_add_norm_sub
    (a b : BoundedCStarSequence A) (n : ℕ) :
    ‖a n‖ ≤ ‖b‖ + ‖(a - b) n‖ := by
  calc
    ‖a n‖ ≤ ‖b n‖ + ‖(a - b) n‖ := by
      nth_rewrite 1 [← add_sub_cancel (b n) (a n)]
      exact norm_add_le _ _
    _ ≤ ‖b‖ + ‖(a - b) n‖ :=
      add_le_add (boundedCStarSequence_coord_norm_le A b n) le_rfl

omit [∀ n, Nontrivial (A n)] in
private theorem eventually_cStarNorm_lt_of_sub_isNull
    (a b : BoundedCStarSequence A)
    (hab : IsNullCStarSequence A l (a - b)) {y : ℝ} (hy : ‖b‖ < y) :
    ∀ᶠ n in l, ‖a n‖ < y := by
  have hev : ∀ᶠ n in l, ‖(a - b) n‖ < y - ‖b‖ :=
    eventually_norm_sub_lt_of_isNull A l a b hab (sub_pos.mpr hy)
  filter_upwards [hev] with n hn
  exact (cStarNorm_le_norm_add_norm_sub A a b n).trans_lt (by linarith)

omit [∀ n, Nontrivial (A n)] in
private theorem cStarSequenceFilterNorm_le_norm_of_sub_isNull [l.NeBot]
    (a b : BoundedCStarSequence A)
    (hab : IsNullCStarSequence A l (a - b)) :
    cStarSequenceFilterNorm A l a ≤ ‖b‖ := by
  apply (Filter.limsup_le_iff
    (cStarNorm_isCoboundedUnder A l a) (cStarNorm_isBoundedUnder A l a)).mpr
  intro y hy
  exact eventually_cStarNorm_lt_of_sub_isNull A l a b hab hy

private theorem cStarSequenceFilterNorm_le_norm_of_mk_eq [l.NeBot]
    (a b : BoundedCStarSequence A)
    (hb : Ideal.Quotient.mk (nullCStarSequenceIdeal A l) b =
      Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a) :
    cStarSequenceFilterNorm A l a ≤ ‖b‖ := by
  have hba : b - a ∈ nullCStarSequenceIdeal A l :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem b a).mp hb
  have hab : a - b ∈ nullCStarSequenceIdeal A l := by
    simpa [neg_sub] using (nullCStarSequenceIdeal A l).neg_mem hba
  exact cStarSequenceFilterNorm_le_norm_of_sub_isNull A l a b hab

private theorem cStarSequenceFilterNorm_le_corona_mk [l.NeBot]
    (a : BoundedCStarSequence A) :
    cStarSequenceFilterNorm A l a ≤
      ‖Ideal.Quotient.mk (nullCStarSequenceIdeal A l) a‖ := by
  apply (QuotientAddGroup.le_norm_iff).mpr
  intro b hb
  exact cStarSequenceFilterNorm_le_norm_of_mk_eq A l a b hb

/-- **The norm in the reduced product is the limsup of the coordinate
norms.**  This is the printed formula, for an arbitrary nontrivial filter. -/
theorem norm_cStarProductCorona_quotient_eq_limsup [l.NeBot]
    (a : BoundedCStarSequence A) :
    ‖cStarProductCoronaQuotient A l a‖ =
      Filter.limsup (fun n ↦ ‖a n‖) l :=
  le_antisymm (cStarProductCorona_mk_le_filterNorm A l a)
    (cStarSequenceFilterNorm_le_corona_mk A l a)

end

end PolarLiftingGeneralCStar
end GroupApproximation
