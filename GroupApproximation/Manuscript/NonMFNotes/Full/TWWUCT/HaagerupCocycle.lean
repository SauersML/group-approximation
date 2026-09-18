import GroupApproximation.Sofic.AmenableActionSofic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Følner data, translations and jumps for the Haagerup cocycle

Lane TWWUCT (work order WO-TWWCore-2).  `non_mf_group_notes.tex` (L1376--1378)
applies Tikuisis--White--Winter to the reduced group C⋆-algebra of an amenable
group.  That needs the UCT for `C⋆_r(G)`.  The UCT comes from Tu (K-Theory 16
(1999), Prop. 10.7), or from Higson--Kasparov (Invent. Math. 144 (2001),
Thm. 1.1): a group with the Haagerup property has `γ = 1`.  This file and
`HaagerupProper` prove the geometric input to that argument: a countable
amenable group has the Haagerup property (Bekka--Chérix--Valette, *Proper affine
isometric actions of amenable groups*, 1995).

This file supplies the ingredients.

* `lpReindex`: reindexing real `ℓ²` along an equivalence, as a linear isometry.
* `translation`: the orthogonal representation `(π_g ξ)(n, x) = ξ(n, g⁻¹x)` on
  `CocycleSpace G = ℓ²(ℕ × G, ℝ)`.
* `FolnerData`: an enumeration `sₖ` of `G` and Følner sets `Aₙ` whose boundaries
  under `s₀, …, sₙ₋₁` and their inverses have relative size less than `4⁻ⁿ`.
  `exists_folnerData` builds it from `AmenableActionSofic.exists_folner`.
* `jump A g x = 1_A(g⁻¹x) - 1_A(x)`, with the cocycle identity `jump_mul` and
  the boundary estimate `sum_jump_sq_le`.
-/

namespace GroupApproximation.Full.TWWUCT

open scoped ENNReal InnerProductSpace

noncomputable section

universe u

/-! ## Reindexing real `ℓ²` -/

section Reindex

variable {α β : Type*}

/-- Reindexing real `ℓ²` along an equivalence preserves square-summability. -/
theorem memℓp_two_comp_equiv (e : α ≃ β) (f : lp (fun _ : α ↦ ℝ) 2) :
    Memℓp (fun b : β ↦ f (e.symm b)) 2 := by
  apply memℓp_gen
  exact (Equiv.summable_iff e.symm).2
    ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp f))

/-- The linear equivalence of real `ℓ²` induced by reindexing. -/
def lpReindexLinear (e : α ≃ β) :
    lp (fun _ : α ↦ ℝ) 2 ≃ₗ[ℝ] lp (fun _ : β ↦ ℝ) 2 where
  toFun f := ⟨fun b ↦ f (e.symm b), memℓp_two_comp_equiv e f⟩
  invFun f := ⟨fun a ↦ f (e.symm.symm a), memℓp_two_comp_equiv e.symm f⟩
  map_add' f g := by
    apply lp.ext
    funext b
    change (⇑(f + g)) (e.symm b) = f (e.symm b) + g (e.symm b)
    rw [lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext b
    change (⇑(c • f)) (e.symm b) = c • f (e.symm b)
    rw [lp.coeFn_smul, Pi.smul_apply]
  left_inv f := by
    apply lp.ext
    funext a
    change f (e.symm (e.symm.symm a)) = f a
    rw [Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv f := by
    apply lp.ext
    funext b
    change f (e.symm.symm (e.symm b)) = f b
    rw [Equiv.symm_symm, Equiv.apply_symm_apply]

/-- Reindexing real `ℓ²` along an equivalence is a linear isometry. -/
def lpReindex (e : α ≃ β) : lp (fun _ : α ↦ ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : β ↦ ℝ) 2 :=
  (lpReindexLinear e).isometryOfInner (by
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    exact Equiv.tsum_eq e.symm fun a ↦ ⟪f a, g a⟫_ℝ)

@[simp]
theorem lpReindex_apply (e : α ≃ β) (f : lp (fun _ : α ↦ ℝ) 2) (b : β) :
    lpReindex e f b = f (e.symm b) :=
  rfl

end Reindex

/-- For a real number, `r ^ (2 : ℝ≥0∞).toReal = r ^ 2`. -/
theorem rpow_two_toReal (r : ℝ) : r ^ (2 : ℝ≥0∞).toReal = r ^ 2 := by
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two]

/-- For a real number, `‖r‖ ^ (2 : ℝ≥0∞).toReal = r ^ 2`. -/
theorem norm_rpow_two_toReal (r : ℝ) : ‖r‖ ^ (2 : ℝ≥0∞).toReal = r ^ 2 := by
  rw [rpow_two_toReal, Real.norm_eq_abs, sq_abs]

/-! ## The translation representation -/

section Translation

variable {G : Type u} [Group G]

/-- The Hilbert space `ℓ²(ℕ × G, ℝ)` carrying the Haagerup cocycle. -/
abbrev CocycleSpace (G : Type u) := lp (fun _ : ℕ × G ↦ ℝ) 2

/-- Left translation in the second coordinate of `ℕ × G`. -/
def shiftEquiv (g : G) : ℕ × G ≃ ℕ × G where
  toFun i := (i.1, g * i.2)
  invFun i := (i.1, g⁻¹ * i.2)
  left_inv i := Prod.ext rfl (inv_mul_cancel_left g i.2)
  right_inv i := Prod.ext rfl (mul_inv_cancel_left g i.2)

/-- The orthogonal translation representation `(π_g ξ)(n, x) = ξ(n, g⁻¹x)`. -/
def translation (g : G) : CocycleSpace G ≃ₗᵢ[ℝ] CocycleSpace G :=
  lpReindex (shiftEquiv g)

@[simp]
theorem translation_apply (g : G) (ξ : CocycleSpace G) (n : ℕ) (x : G) :
    translation g ξ (n, x) = ξ (n, g⁻¹ * x) :=
  rfl

theorem translation_one (ξ : CocycleSpace G) : translation (1 : G) ξ = ξ := by
  apply lp.ext
  funext i
  obtain ⟨n, x⟩ := i
  change ξ (n, (1 : G)⁻¹ * x) = ξ (n, x)
  rw [inv_one, one_mul]

theorem translation_mul (g h : G) (ξ : CocycleSpace G) :
    translation (g * h) ξ = translation g (translation h ξ) := by
  apply lp.ext
  funext i
  obtain ⟨n, x⟩ := i
  change ξ (n, (g * h)⁻¹ * x) = ξ (n, h⁻¹ * (g⁻¹ * x))
  rw [mul_inv_rev, mul_assoc]

end Translation

/-! ## Følner data -/

section Folner

variable {G : Type u} [Group G]

/-- An enumeration of `G` together with Følner sets `Aₙ`.  The boundaries of
`Aₙ` under `s₀, …, sₙ₋₁` and their inverses have relative size less than
`4⁻ⁿ`. -/
structure FolnerData (G : Type u) [Group G] where
  seq : ℕ → G
  seq_surj : Function.Surjective seq
  sets : ℕ → Finset G
  nonempty : ∀ n, (sets n).Nonempty
  small : ∀ n k, k < n →
    ((AmenableActionSofic.boundary (sets n) (seq k)).card : ℝ) <
        (1 / 4 : ℝ) ^ n * (sets n).card ∧
      ((AmenableActionSofic.boundary (sets n) (seq k)⁻¹).card : ℝ) <
        (1 / 4 : ℝ) ^ n * (sets n).card

/-- A countable amenable group admits Følner data. -/
theorem exists_folnerData [Countable G] (hG : Amenability.IsAmenable G) :
    Nonempty (FolnerData G) := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat G
  have key : ∀ n : ℕ, ∃ A : Finset G, A.Nonempty ∧ ∀ k, k < n →
      ((AmenableActionSofic.boundary A (e k)).card : ℝ) < (1 / 4 : ℝ) ^ n * A.card ∧
        ((AmenableActionSofic.boundary A (e k)⁻¹).card : ℝ) < (1 / 4 : ℝ) ^ n * A.card := by
    intro n
    obtain ⟨A, hA, hsmall⟩ := AmenableActionSofic.exists_folner hG
      ((Finset.range n).image e ∪ (Finset.range n).image fun k => (e k)⁻¹)
      (δ := (1 / 4 : ℝ) ^ n) (by positivity)
    refine ⟨A, hA, fun k hk => ⟨hsmall _ ?_, hsmall _ ?_⟩⟩
    · exact Finset.mem_union_left _
        (Finset.mem_image_of_mem e (Finset.mem_range.mpr hk))
    · exact Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun k => (e k)⁻¹) (Finset.mem_range.mpr hk))
  choose A hA hsmall using key
  exact ⟨{ seq := e, seq_surj := he, sets := A, nonempty := hA, small := hsmall }⟩

end Folner

/-! ## The jump function -/

section Jump

variable {G : Type u} [Group G]

open Classical in
/-- `jump A g x = 1_A(g⁻¹x) - 1_A(x)`, the coboundary of the indicator of `A`. -/
def jump (A : Finset G) (g x : G) : ℝ :=
  (if g⁻¹ * x ∈ A then 1 else 0) - (if x ∈ A then 1 else 0)

theorem jump_one (A : Finset G) (x : G) : jump A 1 x = 0 := by
  unfold jump
  rw [inv_one, one_mul, sub_self]

theorem jump_mul (A : Finset G) (g h x : G) :
    jump A (g * h) x = jump A h (g⁻¹ * x) + jump A g x := by
  unfold jump
  rw [mul_inv_rev, mul_assoc]
  ring

/-- Over any finite window, the squared jump is bounded by the two boundaries. -/
theorem sum_jump_sq_le (A : Finset G) (g : G) (X : Finset G) :
    ∑ x ∈ X, jump A g x ^ 2 ≤
      ((AmenableActionSofic.boundary A g).card : ℝ) +
        (AmenableActionSofic.boundary A g⁻¹).card := by
  classical
  have hpt : ∀ x, jump A g x ^ 2 ≤
      (if x ∈ (AmenableActionSofic.boundary A g).image (g * ·) then (1 : ℝ) else 0) +
        (if x ∈ AmenableActionSofic.boundary A g⁻¹ then (1 : ℝ) else 0) := by
    intro x
    unfold jump
    by_cases h1 : g⁻¹ * x ∈ A <;> by_cases h2 : x ∈ A
    · rw [if_pos h1, if_pos h2]
      split_ifs <;> norm_num
    · have hx : x ∈ (AmenableActionSofic.boundary A g).image (g * ·) :=
        Finset.mem_image.mpr ⟨g⁻¹ * x,
          AmenableActionSofic.mem_boundary.mpr ⟨h1, by rwa [mul_inv_cancel_left]⟩,
          mul_inv_cancel_left g x⟩
      rw [if_pos h1, if_neg h2, if_pos hx]
      split_ifs <;> norm_num
    · have hx : x ∈ AmenableActionSofic.boundary A g⁻¹ :=
        AmenableActionSofic.mem_boundary.mpr ⟨h2, h1⟩
      rw [if_neg h1, if_pos h2, if_pos hx]
      split_ifs <;> norm_num
    · rw [if_neg h1, if_neg h2]
      split_ifs <;> norm_num
  have hind : ∀ S : Finset G, ∑ x ∈ X, (if x ∈ S then (1 : ℝ) else 0) ≤ (S.card : ℝ) := by
    intro S
    rw [Finset.sum_boole]
    refine Nat.cast_le.mpr (Finset.card_le_card ?_)
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  calc ∑ x ∈ X, jump A g x ^ 2
      ≤ ∑ x ∈ X, ((if x ∈ (AmenableActionSofic.boundary A g).image (g * ·) then (1 : ℝ) else 0)
          + (if x ∈ AmenableActionSofic.boundary A g⁻¹ then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ x ∈ X, (if x ∈ (AmenableActionSofic.boundary A g).image (g * ·) then (1 : ℝ) else 0)
          + ∑ x ∈ X, (if x ∈ AmenableActionSofic.boundary A g⁻¹ then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (((AmenableActionSofic.boundary A g).image (g * ·)).card : ℝ)
          + (AmenableActionSofic.boundary A g⁻¹).card :=
        add_le_add (hind _) (hind _)
    _ ≤ ((AmenableActionSofic.boundary A g).card : ℝ)
          + (AmenableActionSofic.boundary A g⁻¹).card :=
        add_le_add (Nat.cast_le.mpr Finset.card_image_le) le_rfl

end Jump

end

end GroupApproximation.Full.TWWUCT
