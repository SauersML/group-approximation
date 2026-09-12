import GroupApproximation.Analysis.PowersAveragingComposition
import GroupApproximation.Analysis.PowersAveragingFromPowersProperty

/-!
# From single-conjugacy-class averaging to the full averaging estimate

Powers' condition in its **weak** form controls only finite sets lying inside a
single conjugacy class, and that is the form the literature transfers along a
normal subgroup with trivial centraliser.  This module shows that the weakening
costs nothing on the analytic side: if every element of the group algebra
supported in one non-identity conjugacy class can be averaged down to arbitrarily
small norm, then so can every element of the kernel of the canonical trace, which
is `PowersAveragingEstimate`.

## Why the reduction works

Three facts, and all three are theorems here:

* conjugation preserves conjugacy classes, so averaging maps a combination of
  translations by members of one class to another such combination
  (`average_conjTranslationSum`);
* averaging is a contraction (`norm_reducedAverage_le`), so a bound already
  achieved is not destroyed by a later averaging;
* the composition of two averagings is a single averaging
  (`reducedAverage_comp`), so the whole iteration ends inside the shape
  `PowersAveragingEstimate` asks for.

Given those, the classes present in the support of a finitely supported element
can be killed one at a time, and the composite average is small on all of them
at once.

## The statement of the hypothesis

`SingleClassAveragingEstimate` deliberately names the *analytic* consequence of
the weak Powers property rather than the group-theoretic condition itself.  That
keeps this development independent of a definition this repository has not been
able to quote from a source; when it is quoted, connecting it to this Prop is one
lemma, and nothing here has to change.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra`; certifies no printed sentence on
its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

universe u

noncomputable section

variable (G : Type u) [Group G]

/-! ## Elements supported in one conjugacy class -/

/-- `x` is a finite `ℂ`-combination of translations by members of the conjugacy
class `t`.  Coefficients are allowed to vanish off the class, which is what lets
a fibre of a larger combination be presented without reindexing. -/
def IsConjClassCombination (t : ConjClasses G) (x : ReducedGroupCStar G) : Prop :=
  ∃ (m : ℕ) (c : Fin m → ℂ) (γ : Fin m → G),
    (∀ j, c j = 0 ∨ ConjClasses.mk (γ j) = t) ∧
      x = ∑ j : Fin m, c j • reducedLeftRegular G (γ j)

/-- **The averaging estimate for one conjugacy class.**  This is the analytic
content of the weak Powers property. -/
def SingleClassAveragingEstimate : Prop :=
  ∀ t : ConjClasses G, t ≠ ConjClasses.mk (1 : G) →
    ∀ x : ReducedGroupCStar G, IsConjClassCombination G t x →
      ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (g : Fin n → G), 0 < n ∧
        ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))‖ ≤ ε

/-- Conjugating stays inside a conjugacy class. -/
theorem conjClasses_mk_conj (x γ : G) :
    ConjClasses.mk (x * γ * x⁻¹) = ConjClasses.mk γ := by
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨⟨x, x⁻¹, by group, by group⟩, by group⟩

/-- **Averaging preserves membership in a single conjugacy class.** -/
theorem isConjClassCombination_average {t : ConjClasses G} {x : ReducedGroupCStar G}
    (hx : IsConjClassCombination G t x) {n : ℕ} (g : Fin n → G) :
    IsConjClassCombination G t
      ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * x * star (reducedLeftRegular G (g i))) := by
  obtain ⟨m, c, γ, hcls, rfl⟩ := hx
  refine ⟨n * m, conjAverageCoeff c n, conjAverageFamily G γ g, fun l ↦ ?_,
    average_conjTranslationSum G c γ g⟩
  rcases hcls (finProdFinEquiv.symm l).2 with hzero | hclass
  · left
    rw [conjAverageCoeff_apply, hzero, mul_zero]
  · right
    rw [conjAverageFamily_conj, conjClasses_mk_conj, hclass]

/-! ## Averaging is additive -/

/-- Averaging distributes over a finite sum. -/
theorem reducedAverage_sum {ι : Type*} (s : Finset ι) (x : ι → ReducedGroupCStar G)
    {n : ℕ} (g : Fin n → G) :
    ((n : ℂ)⁻¹ • ∑ i : Fin n, reducedLeftRegular G (g i) * (∑ t ∈ s, x t) *
        star (reducedLeftRegular G (g i)))
      = ∑ t ∈ s, (n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i) * x t * star (reducedLeftRegular G (g i)) := by
  have hinner : ∀ i : Fin n,
      reducedLeftRegular G (g i) * (∑ t ∈ s, x t) * star (reducedLeftRegular G (g i))
        = ∑ t ∈ s, reducedLeftRegular G (g i) * x t *
            star (reducedLeftRegular G (g i)) := by
    intro i
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun i _ ↦ hinner i, Finset.sum_comm, Finset.smul_sum]

/-! ## One average that is small on a whole finite family -/

/-- **The induction.**  For a finite family of elements, each supported in one
non-identity conjugacy class, there is a *single* average that is small on every
member of the family at once. -/
theorem exists_average_small_on_finset (hcls : SingleClassAveragingEstimate G)
    (S : Finset (ConjClasses G)) (x : ConjClasses G → ReducedGroupCStar G)
    (hne : ∀ t ∈ S, t ≠ ConjClasses.mk (1 : G))
    (hx : ∀ t ∈ S, IsConjClassCombination G t (x t))
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ) (g : Fin n → G), 0 < n ∧
      ∀ t ∈ S, ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * x t * star (reducedLeftRegular G (g i))‖ ≤ η := by
  classical
  induction S using Finset.induction with
  | empty => exact ⟨1, fun _ ↦ (1 : G), one_pos, by simp⟩
  | insert t S' ht ih =>
      obtain ⟨n₁, g₁, hn₁, hb₁⟩ :=
        ih (fun s hs ↦ hne s (Finset.mem_insert_of_mem hs))
          (fun s hs ↦ hx s (Finset.mem_insert_of_mem hs))
      set y : ReducedGroupCStar G := (n₁ : ℂ)⁻¹ • ∑ i : Fin n₁,
        reducedLeftRegular G (g₁ i) * x t * star (reducedLeftRegular G (g₁ i)) with hy
      have hyc : IsConjClassCombination G t y :=
        isConjClassCombination_average G (hx t (Finset.mem_insert_self t S')) g₁
      obtain ⟨n₂, g₂, hn₂, hb₂⟩ :=
        hcls t (hne t (Finset.mem_insert_self t S')) y hyc η hη
      refine ⟨n₂ * n₁, composeFamily G g₁ g₂, Nat.mul_pos hn₂ hn₁, fun s hs ↦ ?_⟩
      have hcomp : ∀ z : ReducedGroupCStar G,
          ((n₂ * n₁ : ℕ) : ℂ)⁻¹ • ∑ l : Fin (n₂ * n₁),
              reducedLeftRegular G (composeFamily G g₁ g₂ l) * z *
                star (reducedLeftRegular G (composeFamily G g₁ g₂ l))
            = (n₂ : ℂ)⁻¹ • ∑ j : Fin n₂, reducedLeftRegular G (g₂ j) *
                ((n₁ : ℂ)⁻¹ • ∑ i : Fin n₁,
                  reducedLeftRegular G (g₁ i) * z * star (reducedLeftRegular G (g₁ i))) *
                star (reducedLeftRegular G (g₂ j)) :=
        fun z ↦ (reducedAverage_comp G z g₁ g₂).symm
      rw [hcomp (x s)]
      rcases Finset.mem_insert.mp hs with rfl | hs'
      · rw [← hy]
        exact hb₂
      · exact le_trans (norm_reducedAverage_le G _ hn₂ g₂) (hb₁ s hs')

/-! ## The class decomposition of a finitely supported element -/

/-- Only the identity is conjugate to the identity. -/
theorem eq_one_of_conjClasses_mk_eq_one {g : G}
    (h : ConjClasses.mk g = ConjClasses.mk (1 : G)) : g = 1 := by
  rw [ConjClasses.mk_eq_mk_iff_isConj] at h
  exact isConj_one_right.mp h

/-! ## The estimate -/

/-- **The full averaging estimate follows from the single-class one.**

The support of an approximant meets finitely many conjugacy classes; averaging
preserves that decomposition, is a contraction, and composes, so the classes can
be killed one at a time and the composite is still one average. -/
set_option maxHeartbeats 1000000 in
theorem powersAveragingEstimate_of_singleClass
    (h : SingleClassAveragingEstimate G) : PowersAveragingEstimate G := by
  classical
  intro a hτa ε hε
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  -- Approximate, and delete the identity coefficient, exactly as in
  -- `powersAveragingEstimate_of_powersProperty`.
  obtain ⟨m, c, γ, happrox⟩ := exists_translationSum_approx G a.2 hδ
  set b : ReducedGroupCStar G := ∑ j : Fin m, c j • reducedLeftRegular G (γ j) with hbdef
  have hbcoe : (b : GroupHilbert G →L[ℂ] GroupHilbert G)
      = ∑ j : Fin m, c j • leftRegularOperator G (γ j) := by
    rw [hbdef]
    exact coe_translationSum G c γ
  have hab : ‖a - b‖ < δ := by
    have hsub : ((a - b : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G)
        = (a : GroupHilbert G →L[ℂ] GroupHilbert G)
          - ∑ j : Fin m, c j • leftRegularOperator G (γ j) := by
      have hmap := map_sub (reducedInclusion G) a b
      rw [reducedInclusion_apply, reducedInclusion_apply, reducedInclusion_apply,
        hbcoe] at hmap
      exact hmap
    have hnorm := happrox
    rw [← hsub, norm_coe_reducedGroupCStar] at hnorm
    exact hnorm
  set c' : Fin m → ℂ := fun j ↦ if γ j = 1 then 0 else c j with hc'
  set b₀ : ReducedGroupCStar G := ∑ j : Fin m, c' j • reducedLeftRegular G (γ j)
    with hb₀
  set κ : ℂ := ∑ j : Fin m, (if γ j = 1 then c j else 0) with hκdef
  have hsplit : b = b₀ + κ • 1 := by
    rw [hbdef, hb₀, hκdef, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hγ : γ j = 1
    · rw [hc']
      simp [hγ]
    · simp [hc', hγ]
  have hτb₀ : canonicalFaithfulTracialState G b₀ = 0 := by
    have hlin : canonicalCoefficientAtOne G b₀
        = ∑ j : Fin m,
          c' j * canonicalCoefficientAtOne G (reducedLeftRegular G (γ j)) := by
      rw [hb₀, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
    show canonicalCoefficientAtOne G b₀ = 0
    rw [hlin]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [canonicalCoefficientAtOne_reducedLeftRegular]
    by_cases hγ : γ j = 1
    · rw [hc']
      simp [hγ]
    · simp [hγ]
  have hτb : canonicalFaithfulTracialState G b = κ := by
    have hlin : canonicalCoefficientAtOne G b
        = ∑ j : Fin m,
          c j * canonicalCoefficientAtOne G (reducedLeftRegular G (γ j)) := by
      rw [hbdef, map_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
    show canonicalCoefficientAtOne G b = κ
    rw [hlin, hκdef]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [canonicalCoefficientAtOne_reducedLeftRegular]
    by_cases hγ : γ j = 1 <;> simp [hγ]
  have hκsmall : ‖κ‖ < δ := by
    have hbound : ‖canonicalFaithfulTracialState G (b - a)‖ ≤ ‖b - a‖ :=
      Manuscript.MFRecognition.TensorSynchronization.norm_tracialState_le
        (canonicalFaithfulTracialState G).toTracialState (b - a)
    have heq : canonicalFaithfulTracialState G (b - a) = κ := by
      rw [FaithfulTracialState.map_sub, hτa, hτb, sub_zero]
    rw [heq] at hbound
    calc ‖κ‖ ≤ ‖b - a‖ := hbound
      _ = ‖a - b‖ := by rw [← norm_neg, neg_sub]
      _ < δ := hab
  have hab₀ : ‖a - b₀‖ < 2 * δ := by
    have hdecomp : a - b₀ = (a - b) + κ • (1 : ReducedGroupCStar G) := by
      rw [hsplit]; abel
    have hsmul : ‖κ • (1 : ReducedGroupCStar G)‖ ≤ ‖κ‖ := by
      rw [norm_smul]
      nlinarith [norm_nonneg κ, norm_one_le_one G,
        norm_nonneg (1 : ReducedGroupCStar G)]
    calc ‖a - b₀‖ = ‖(a - b) + κ • (1 : ReducedGroupCStar G)‖ := by rw [hdecomp]
      _ ≤ ‖a - b‖ + ‖κ • (1 : ReducedGroupCStar G)‖ := norm_add_le _ _
      _ < δ + δ :=
          add_lt_add_of_lt_of_le hab (le_of_lt (lt_of_le_of_lt hsmul hκsmall))
      _ = 2 * δ := by ring
  -- Split `b₀` into its conjugacy-class components.
  set T : Finset (ConjClasses G) :=
    Finset.univ.image (fun j : Fin m ↦ ConjClasses.mk (γ j)) with hT
  set S : Finset (ConjClasses G) := T.erase (ConjClasses.mk (1 : G)) with hS
  set x : ConjClasses G → ReducedGroupCStar G := fun t ↦ ∑ j : Fin m,
    (if ConjClasses.mk (γ j) = t then c' j else 0) • reducedLeftRegular G (γ j)
    with hxdef
  have hxone : x (ConjClasses.mk (1 : G)) = 0 := by
    rw [hxdef]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    by_cases hj : ConjClasses.mk (γ j) = ConjClasses.mk (1 : G)
    · rw [if_pos hj, hc']
      simp [eq_one_of_conjClasses_mk_eq_one G hj]
    · rw [if_neg hj, zero_smul]
  have hbig : (∑ t ∈ T, x t) = b₀ := by
    rw [hb₀, hxdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_smul, Finset.sum_ite_eq]
    congr 1
    exact if_pos (by rw [hT]; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  have hdecomp : b₀ = ∑ t ∈ S, x t := by
    rw [hS, Finset.sum_erase _ hxone, hbig]
  have hxne : ∀ t ∈ S, t ≠ ConjClasses.mk (1 : G) := fun t ht ↦
    (Finset.mem_erase.mp ht).1
  have hxcls : ∀ t ∈ S, IsConjClassCombination G t (x t) := by
    intro t _
    refine ⟨m, fun j ↦ if ConjClasses.mk (γ j) = t then c' j else 0, γ, fun j ↦ ?_, rfl⟩
    by_cases hj : ConjClasses.mk (γ j) = t
    · exact Or.inr hj
    · exact Or.inl (if_neg hj)
  -- One average, small on every class at once.
  set η : ℝ := δ / ((S.card : ℝ) + 1) with hηdef
  have hcardpos : (0 : ℝ) < (S.card : ℝ) + 1 := by positivity
  have hη : 0 < η := by rw [hηdef]; positivity
  obtain ⟨n, g, hn, hsmall⟩ :=
    exists_average_small_on_finset G h S x hxne hxcls η hη
  have hcard : (S.card : ℝ) * η ≤ δ := by
    rw [hηdef, ← mul_div_assoc, div_le_iff₀ hcardpos]
    nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) S.card]
  have hb₀est : ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
      reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i))‖ ≤ δ := by
    rw [hdecomp, reducedAverage_sum]
    calc ‖∑ t ∈ S, (n : ℂ)⁻¹ • ∑ i : Fin n,
          reducedLeftRegular G (g i) * x t * star (reducedLeftRegular G (g i))‖
        ≤ ∑ t ∈ S, ‖(n : ℂ)⁻¹ • ∑ i : Fin n,
            reducedLeftRegular G (g i) * x t * star (reducedLeftRegular G (g i))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _t ∈ S, η := Finset.sum_le_sum hsmall
      _ = (S.card : ℝ) * η := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ δ := hcard
  -- The difference is handled by the contraction bound.
  have hdiff : ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))
      = (n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * (a - b₀) * star (reducedLeftRegular G (g i)) := by
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_sub, sub_mul]
  have hdiffbound : ‖((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)))
      - ((n : ℂ)⁻¹ • ∑ i : Fin n,
        reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)))‖
      ≤ ‖a - b₀‖ := by
    rw [hdiff]
    exact norm_reducedAverage_le G (a - b₀) hn g
  refine ⟨n, g, hn, ?_⟩
  set X : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * a * star (reducedLeftRegular G (g i)) with hX
  set Y : ReducedGroupCStar G := (n : ℂ)⁻¹ • ∑ i : Fin n,
    reducedLeftRegular G (g i) * b₀ * star (reducedLeftRegular G (g i)) with hY
  have hXY : (X - Y) + Y = X := by abel
  calc ‖X‖ = ‖(X - Y) + Y‖ := by rw [hXY]
    _ ≤ ‖X - Y‖ + ‖Y‖ := norm_add_le _ _
    _ ≤ ‖a - b₀‖ + δ := add_le_add hdiffbound hb₀est
    _ ≤ 2 * δ + δ := by linarith [hab₀.le]
    _ ≤ ε := by rw [hδdef]; linarith

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms eq_one_of_conjClasses_mk_eq_one
#audit_axioms powersAveragingEstimate_of_singleClass
#audit_axioms IsConjClassCombination
#audit_axioms SingleClassAveragingEstimate
#audit_axioms conjClasses_mk_conj
#audit_axioms isConjClassCombination_average
#audit_axioms reducedAverage_sum
#audit_axioms exists_average_small_on_finset
