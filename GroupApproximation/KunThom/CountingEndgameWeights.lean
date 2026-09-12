import GroupApproximation.Sofic.Asymptotics
import GroupApproximation.Matching.FiniteGroupoidCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr

/-!
# Weights and counts for the counting endgame

The finite endgame `CountingEndgame.exists_bisection_lift` needs, at every
selected object, an orbit count and an isotropy index below `2`.  Kun and Thom
obtain both from cleanliness and from the concentration (4) of orbit sizes and
isotropy orders (arXiv:2608.06222v3, §4, tex lines 1140–1276).  They then bound
the weight of the completion (tex lines 1294–1313).  This file proves the
finite inequalities involved.

* `card_lt_add_of_ratio`: two source orbits, each keeping a `1 - ζ` fraction of
  an ambient orbit that is at least a `1 / ρ` fraction of the image orbit, with
  `ρ < 2 (1 - ζ)`, have more objects together than the image orbit.
* `lt_two_mul_of_ratio`: an image isotropy order at most `ρ < 2` times the
  source order is below twice the source order.
* `sum_compl_image_le`: the weight outside the selected sources `π '' E` is at
  most the weight outside `π '' D` plus `c` times the weight of `D \ E`, when `π`
  is injective on `D` and enlarges weights by at most the factor `c`.
* `sum_filter_image_le`: the objects of `D` sent into a set `T` weigh at most
  `c` times `T`, when `π` shrinks weights by at most the factor `c`.
* `mul_sum_le_of_dirty`: if weights vary by at most the factor `1 - ε` inside
  every orbit, the orbits meeting `B` in more than a `ζ` fraction of their
  objects weigh at most `1 / (ζ (1 - ε))` times `B`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory

universe u v

/-- **Orbit count from concentration.**  If both source orbits keep a `1 - ζ`
fraction of their ambient orbits, each ambient orbit is at least a `1 / ρ`
fraction of the image orbit, and `ρ < 2 (1 - ζ)`, then the image orbit has fewer
objects than the two source orbits together. -/
theorem card_lt_add_of_ratio {oD oX oX' cX cX' : ℕ} {ζ ρ : ℝ} (hρ : 0 < ρ)
    (hζρ : ρ < 2 * (1 - ζ)) (hpos : 0 < oD)
    (hcleanX : (1 - ζ) * (cX : ℝ) ≤ oX) (hcleanX' : (1 - ζ) * (cX' : ℝ) ≤ oX')
    (hratioX : (oD : ℝ) ≤ ρ * cX) (hratioX' : (oD : ℝ) ≤ ρ * cX') :
    oD < oX + oX' := by
  have hζ : 0 ≤ 1 - ζ := by linarith
  have hD : (0 : ℝ) < oD := by exact_mod_cast hpos
  have h₁ : (1 - ζ) * (2 * (oD : ℝ)) ≤ (1 - ζ) * (ρ * ((cX : ℝ) + cX')) :=
    mul_le_mul_of_nonneg_left (by linarith) hζ
  have h₂ : ρ * ((1 - ζ) * ((cX : ℝ) + cX')) ≤ ρ * ((oX : ℝ) + oX') :=
    mul_le_mul_of_nonneg_left (by linarith) hρ.le
  have h₃ : ρ * (oD : ℝ) < 2 * (1 - ζ) * oD := mul_lt_mul_of_pos_right hζρ hD
  have h₄ : ρ * (oD : ℝ) < ρ * ((oX : ℝ) + oX') := by linarith
  exact_mod_cast lt_of_mul_lt_mul_left h₄ hρ.le

/-- **Isotropy index from concentration.**  An image isotropy order at most
`ρ < 2` times a positive source order is below twice the source order. -/
theorem lt_two_mul_of_ratio {kD kX : ℕ} {ρ : ℝ} (hρ : ρ < 2) (hpos : 0 < kX)
    (hratio : (kD : ℝ) ≤ ρ * kX) : kD < 2 * kX := by
  have hX : (0 : ℝ) < kX := by exact_mod_cast hpos
  have h : ρ * (kX : ℝ) < 2 * kX := mul_lt_mul_of_pos_right hρ hX
  have h' : (kD : ℝ) < 2 * kX := by linarith
  exact_mod_cast h'

/-- **Completion weight.**  Let `π` be injective on `D` and enlarge weights by at
most the factor `c`.  The weight outside the selected sources `π '' E` is at most
the weight outside `π '' D` plus `c` times the weight of `D \ E`. -/
theorem sum_compl_image_le {I : Type u} [Fintype I] [DecidableEq I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (D E : Finset I) (π : I → I) (hπ : Set.InjOn π (D : Set I))
    {c : ℝ} (hc : ∀ i ∈ D, w (π i) ≤ c * w i) :
    ∑ j ∈ Finset.univ \ E.image π, w j ≤
      ∑ j ∈ Finset.univ \ D.image π, w j + c * ∑ i ∈ D \ E, w i := by
  have hsub : Finset.univ \ E.image π ⊆ (Finset.univ \ D.image π) ∪ (D \ E).image π := by
    intro j hj
    by_cases hjR : j ∈ D.image π
    · apply Finset.mem_union_right
      obtain ⟨i, hiD, hij⟩ := Finset.mem_image.mp hjR
      refine Finset.mem_image.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hiD, fun hiE ↦ ?_⟩, hij⟩
      apply (Finset.mem_sdiff.mp hj).2
      rw [← hij]
      exact Finset.mem_image_of_mem π hiE
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjR⟩)
  have hle : ∑ j ∈ Finset.univ \ E.image π, w j ≤
      ∑ j ∈ (Finset.univ \ D.image π) ∪ (D \ E).image π, w j :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ ↦ hw j
  have hunion : (∑ j ∈ (Finset.univ \ D.image π) ∪ (D \ E).image π, w j) +
      ∑ j ∈ (Finset.univ \ D.image π) ∩ (D \ E).image π, w j =
        (∑ j ∈ Finset.univ \ D.image π, w j) + ∑ j ∈ (D \ E).image π, w j :=
    Finset.sum_union_inter
  have hinter : 0 ≤ ∑ j ∈ (Finset.univ \ D.image π) ∩ (D \ E).image π, w j :=
    Finset.sum_nonneg fun j _ ↦ hw j
  have himage : ∑ j ∈ (D \ E).image π, w j = ∑ i ∈ D \ E, w (π i) := by
    apply Finset.sum_image
    intro x hx y hy hxy
    exact hπ (Finset.mem_coe.mpr (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).1)
      (Finset.mem_coe.mpr (Finset.mem_sdiff.mp (Finset.mem_coe.mp hy)).1) hxy
  have hmono : ∑ i ∈ D \ E, w (π i) ≤ c * ∑ i ∈ D \ E, w i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi ↦ hc i (Finset.mem_sdiff.mp hi).1
  linarith

/-- **Preimage weight.**  Let `π` be injective on `D` and shrink weights by at
most the factor `c ≥ 0`.  The objects of `D` sent into `T` weigh at most `c` times
the weight of `T`. -/
theorem sum_filter_image_le {I : Type u} [DecidableEq I] (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (D T : Finset I) (π : I → I) (hπ : Set.InjOn π (D : Set I))
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ i ∈ D, w i ≤ c * w (π i)) :
    ∑ i ∈ D.filter (fun i ↦ π i ∈ T), w i ≤ c * ∑ j ∈ T, w j := by
  have hinj : Set.InjOn π ((D.filter fun i ↦ π i ∈ T : Finset I) : Set I) := by
    intro x hx y hy hxy
    exact hπ (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
      (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1) hxy
  calc ∑ i ∈ D.filter (fun i ↦ π i ∈ T), w i
      ≤ ∑ i ∈ D.filter (fun i ↦ π i ∈ T), c * w (π i) :=
        Finset.sum_le_sum fun i hi ↦ hc i (Finset.mem_filter.mp hi).1
    _ = c * ∑ j ∈ (D.filter fun i ↦ π i ∈ T).image π, w j := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ c * ∑ j ∈ T, w j := by
        apply mul_le_mul_of_nonneg_left _ hc0
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj
          rw [← hij]
          exact (Finset.mem_filter.mp hi).2
        · intro j _ _
          exact hw j

/-- **Clean orbits.**  Suppose weights vary by at most the factor `1 - ε` inside
every orbit of a finite groupoid.  If every orbit of an object in `dirty` meets
`B` in more than a `ζ` fraction of its objects, then `ζ (1 - ε)` times the weight
of `dirty` is at most the weight of `B`. -/
theorem mul_sum_le_of_dirty {C : Type u} [Groupoid.{v} C] [Fintype C] [DecidableEq C]
    (w : C → ℝ) (hw : ∀ X, 0 ≤ w X) (B dirty : Finset C) {ε ζ : ℝ} (hε : 0 ≤ 1 - ε)
    (hcomp : ∀ X, ∀ Y ∈ FiniteGroupoid.orbit X, (1 - ε) * w X ≤ w Y)
    (hdirty : ∀ X ∈ dirty, ζ * ((FiniteGroupoid.orbit X).card : ℝ) <
      ((FiniteGroupoid.orbit X ∩ B).card : ℝ)) :
    ζ * (1 - ε) * ∑ X ∈ dirty, w X ≤ ∑ Y ∈ B, w Y := by
  have hcard : ∀ X : C, (0 : ℝ) < (FiniteGroupoid.orbit X).card := fun X ↦ by
    exact_mod_cast Finset.card_pos.mpr ⟨X, FiniteGroupoid.self_mem_orbit X⟩
  have hsymm : ∀ X Y : C, Y ∈ FiniteGroupoid.orbit X ↔ X ∈ FiniteGroupoid.orbit Y := by
    intro X Y
    rw [FiniteGroupoid.mem_orbit, FiniteGroupoid.mem_orbit]
    exact ⟨fun ⟨f⟩ ↦ ⟨inv f⟩, fun ⟨f⟩ ↦ ⟨inv f⟩⟩
  have hstep : ∀ X : C, ζ * ((FiniteGroupoid.orbit X).card : ℝ) <
      ((FiniteGroupoid.orbit X ∩ B).card : ℝ) →
      ζ * (1 - ε) * w X ≤
        (∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y) / (FiniteGroupoid.orbit X).card := by
    intro X hX
    rw [le_div_iff₀ (hcard X)]
    have hsum : ((FiniteGroupoid.orbit X ∩ B).card : ℝ) * ((1 - ε) * w X) ≤
        ∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y := by
      calc ((FiniteGroupoid.orbit X ∩ B).card : ℝ) * ((1 - ε) * w X)
          = ∑ _Y ∈ FiniteGroupoid.orbit X ∩ B, (1 - ε) * w X := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y :=
            Finset.sum_le_sum fun Y hY ↦ hcomp X Y (Finset.mem_inter.mp hY).1
    have hmul := mul_le_mul_of_nonneg_right hX.le (mul_nonneg hε (hw X))
    linarith
  have hmem : ∀ X Y, X ∈ (Finset.univ : Finset C) ∧ Y ∈ FiniteGroupoid.orbit X ∩ B ↔
      X ∈ FiniteGroupoid.orbit Y ∧ Y ∈ B := by
    intro X Y
    rw [Finset.mem_inter, hsymm X Y]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ X, h⟩⟩
  have hdouble : ∑ X : C,
      (∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y) / (FiniteGroupoid.orbit X).card =
        ∑ Y ∈ B, w Y := by
    simp only [Finset.sum_div]
    rw [Finset.sum_comm' hmem]
    refine Finset.sum_congr rfl fun Y _ ↦ ?_
    have hconst : ∀ X ∈ FiniteGroupoid.orbit Y,
        w Y / ((FiniteGroupoid.orbit X).card : ℝ) = w Y / (FiniteGroupoid.orbit Y).card := by
      intro X hX
      obtain ⟨f⟩ := (FiniteGroupoid.mem_orbit Y X).mp hX
      rw [FiniteGroupoid.orbit_eq_of_hom f]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_div_assoc',
      mul_div_cancel_left₀ _ (hcard Y).ne']
  calc ζ * (1 - ε) * ∑ X ∈ dirty, w X
      = ∑ X ∈ dirty, ζ * (1 - ε) * w X := by rw [Finset.mul_sum]
    _ ≤ ∑ X ∈ dirty,
          (∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y) / (FiniteGroupoid.orbit X).card :=
        Finset.sum_le_sum fun X hX ↦ hstep X (hdirty X hX)
    _ ≤ ∑ X : C,
          (∑ Y ∈ FiniteGroupoid.orbit X ∩ B, w Y) / (FiniteGroupoid.orbit X).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ dirty) fun X _ _ ↦
          div_nonneg (Finset.sum_nonneg fun Y _ ↦ hw Y) (hcard X).le
    _ = ∑ Y ∈ B, w Y := hdouble

end CountingEndgame
end GroupApproximation
