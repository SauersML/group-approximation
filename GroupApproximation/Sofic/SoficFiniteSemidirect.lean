import GroupApproximation.Sofic.Sofic
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Soficity of finite semidirect extensions

This file proves, from the local permutation-model definition, the permanence
fact needed by the flip argument for symmetric doubles: if `N` is sofic and a
finite group `K` acts on `N`, then `N ⋊ K` is sofic.

No closure theorem is imported.  The model is the elementary induced model on
`Y × K`.  On the fibre indexed by `q`, an element `g = (n,k)` uses the
permutation assigned to

`φ ((k*q)⁻¹) n`

and sends that fibre to the fibre `k*q`.  The cocycle identity for these
labels turns the multiplicative error into the average of the errors in the
base model.  Distinct finite coordinates separate every point; equal finite
coordinates reduce separation to the corresponding average downstairs.
-/

namespace GroupApproximation

open Finset

variable {N : Type*} {K : Type} [Group N] [Group K]

/-- The permutation induced on `Y × K` by a not-necessarily-multiplicative
permutation-valued map on the normal factor. -/
def inducedSemidirectPerm (Y : Type*) (φ : K →* MulAut N)
    (σ : N → Equiv.Perm Y) (g : N ⋊[φ] K) : Equiv.Perm (Y × K) where
  toFun p :=
    (σ (φ ((g.right * p.2)⁻¹) g.left) p.1, g.right * p.2)
  invFun p :=
    ((σ (φ p.2⁻¹ g.left))⁻¹ p.1, g.right⁻¹ * p.2)
  left_inv p := by
    apply Prod.ext
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · simp
    · simp

@[simp] theorem inducedSemidirectPerm_apply (Y : Type*)
    (φ : K →* MulAut N) (σ : N → Equiv.Perm Y)
    (g : N ⋊[φ] K) (p : Y × K) :
    inducedSemidirectPerm Y φ σ g p =
      (σ (φ ((g.right * p.2)⁻¹) g.left) p.1, g.right * p.2) := rfl

/-- The finite induced carrier. -/
abbrev inducedSemidirectModel (Y : FiniteModel) (K : Type)
    [Fintype K] [DecidableEq K] : FiniteModel :=
  ⟨Y × K, inferInstance, inferInstance⟩

@[simp] theorem card_inducedSemidirectModel (Y : FiniteModel) (K : Type)
    [Fintype K] [DecidableEq K] :
    Fintype.card (inducedSemidirectModel Y K) =
      Fintype.card Y * Fintype.card K := by
  exact Fintype.card_prod _ _

/-- The induced label satisfies the cocycle identity for multiplication in a
semidirect product. -/
theorem inducedSemidirect_label_mul (φ : K →* MulAut N)
    (g h : N ⋊[φ] K) (q : K) :
    φ (((g * h).right * q)⁻¹) (g * h).left =
      φ ((g.right * (h.right * q))⁻¹) g.left *
        φ ((h.right * q)⁻¹) h.left := by
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
  have hfirst : g.right * h.right * q = g.right * (h.right * q) := by group
  rw [hfirst]
  congr 1
  rw [← MulAut.mul_apply]
  rw [← φ.map_mul]
  congr 1
  group

/-- If two induced permutations have the same finite coordinate, their
normalized Hamming distance is the average of the fibrewise base distances. -/
theorem hammingDistance_inducedSemidirectPerm_of_right_eq
    (Y : FiniteModel) [Fintype K] [DecidableEq K]
    (φ : K →* MulAut N) (σ : N → Equiv.Perm Y)
    {g h : N ⋊[φ] K} (hright : g.right = h.right)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (inducedSemidirectModel Y K)
        (inducedSemidirectPerm Y φ σ g)
        (inducedSemidirectPerm Y φ σ h) =
      (∑ q : K, hammingDistance Y
        (σ (φ ((g.right * q)⁻¹) g.left))
        (σ (φ ((g.right * q)⁻¹) h.left))) / Fintype.card K := by
  classical
  let D : Finset (Y × K) := hammingDisagreement
    (inducedSemidirectPerm Y φ σ g) (inducedSemidirectPerm Y φ σ h)
  have hfiber (q : K) :
      D.filter (fun p ↦ p.2 = q) =
        (hammingDisagreement
          (σ (φ ((g.right * q)⁻¹) g.left))
          (σ (φ ((g.right * q)⁻¹) h.left))).map
            ⟨fun y ↦ (y, q), fun _ _ e ↦ congrArg Prod.fst e⟩ := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_map,
      mem_hammingDisagreement, D]
    constructor
    · rintro ⟨hp, rfl⟩
      refine ⟨p.1, ?_, rfl⟩
      simpa [hright] using hp
    · rintro ⟨y, hy, hpeq⟩
      subst p
      exact ⟨by simpa [hright] using hy, rfl⟩
  have hcardD : D.card = ∑ q : K,
      (hammingDisagreement
        (σ (φ ((g.right * q)⁻¹) g.left))
        (σ (φ ((g.right * q)⁻¹) h.left))).card := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (s := D)
      (t := (Finset.univ : Finset K)) (g := Prod.snd)
    simp only [Finset.mem_univ, Finset.filter_true] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hfiber q, Finset.card_map]
  rw [hammingDistance]
  change (D.card : ℝ) / Fintype.card (Y × K) = _
  rw [Fintype.card_prod]
  rw [hcardD]
  push_cast
  simp only [hammingDistance]
  rw [Finset.sum_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  field_simp

/-- Different finite coordinates move every point of the induced carrier. -/
theorem hammingDistance_inducedSemidirectPerm_of_right_ne
    (Y : FiniteModel) [Fintype K] [DecidableEq K]
    (φ : K →* MulAut N) (σ : N → Equiv.Perm Y)
    {g h : N ⋊[φ] K} (hright : g.right ≠ h.right)
    (hY : 0 < Fintype.card Y) :
    hammingDistance (inducedSemidirectModel Y K)
        (inducedSemidirectPerm Y φ σ g)
        (inducedSemidirectPerm Y φ σ h) = 1 := by
  classical
  have hdis : hammingDisagreement
      (inducedSemidirectPerm Y φ σ g)
      (inducedSemidirectPerm Y φ σ h) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    rw [mem_hammingDisagreement]
    intro hp
    apply hright
    exact mul_right_cancel (congrArg Prod.snd hp)
  rw [hammingDistance, hdis, Finset.card_univ]
  exact div_self (by
    rw [Fintype.card_prod]
    exact_mod_cast (Nat.mul_pos hY (Fintype.card_pos_iff.mpr ⟨1⟩)).ne')

/-- Multiplication of induced permutations has exactly the fibrewise defect
of the base map. -/
theorem hammingDistance_inducedSemidirectPerm_mul
    (Y : FiniteModel) [Fintype K] [DecidableEq K]
    (φ : K →* MulAut N) (σ : N → Equiv.Perm Y)
    (g h : N ⋊[φ] K) (hY : 0 < Fintype.card Y) :
    hammingDistance (inducedSemidirectModel Y K)
        (inducedSemidirectPerm Y φ σ (g * h))
        (inducedSemidirectPerm Y φ σ g *
          inducedSemidirectPerm Y φ σ h) =
      (∑ q : K, hammingDistance Y
        (σ (φ (((g * h).right * q)⁻¹) (g * h).left))
        (σ (φ ((g.right * (h.right * q))⁻¹) g.left) *
          σ (φ ((h.right * q)⁻¹) h.left))) / Fintype.card K := by
  classical
  let p : Equiv.Perm (Y × K) :=
    inducedSemidirectPerm Y φ σ g * inducedSemidirectPerm Y φ σ h
  have hp (x : Y × K) : p x =
      ((σ (φ ((g.right * (h.right * x.2))⁻¹) g.left) *
        σ (φ ((h.right * x.2)⁻¹) h.left)) x.1,
        (g * h).right * x.2) := by
    simp [p, Equiv.Perm.mul_apply, mul_assoc]
  let D : Finset (Y × K) := hammingDisagreement
    (inducedSemidirectPerm Y φ σ (g * h)) p
  have hfiber (q : K) :
      D.filter (fun x ↦ x.2 = q) =
        (hammingDisagreement
          (σ (φ (((g * h).right * q)⁻¹) (g * h).left))
          (σ (φ ((g.right * (h.right * q))⁻¹) g.left) *
            σ (φ ((h.right * q)⁻¹) h.left))).map
              ⟨fun y ↦ (y, q), fun _ _ e ↦ congrArg Prod.fst e⟩ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map,
      mem_hammingDisagreement, D]
    constructor
    · rintro ⟨hx, hxq⟩
      refine ⟨x.1, ?_, Prod.ext rfl hxq.symm⟩
      intro heq
      apply hx
      rw [hp]
      apply Prod.ext
      · simpa [hxq] using heq
      · simp [hxq]
    · rintro ⟨y, hy, hxeq⟩
      refine ⟨?_, (congrArg Prod.snd hxeq).symm⟩
      rw [← hxeq]
      change inducedSemidirectPerm Y φ σ (g * h) (y, q) ≠ p (y, q)
      rw [hp]
      intro heq
      exact hy (congrArg Prod.fst heq)
  have hcardD : D.card = ∑ q : K,
      (hammingDisagreement
        (σ (φ (((g * h).right * q)⁻¹) (g * h).left))
        (σ (φ ((g.right * (h.right * q))⁻¹) g.left) *
          σ (φ ((h.right * q)⁻¹) h.left))).card := by
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (s := D)
      (t := (Finset.univ : Finset K)) (g := Prod.snd)
    simp only [Finset.mem_univ, Finset.filter_true] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro q _
    rw [hfiber q, Finset.card_map]
  rw [hammingDistance]
  change (D.card : ℝ) / Fintype.card (Y × K) = _
  rw [Fintype.card_prod]
  rw [hcardD]
  push_cast
  simp only [hammingDistance]
  rw [Finset.sum_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro q _
  field_simp

/-- **Finite semidirect permanence.** -/
theorem isSofic_semidirectProduct_of_finite (φ : K →* MulAut N)
    [Finite K] (hN : IsSofic N) : IsSofic (N ⋊[φ] K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  intro F ε hε
  let T : Finset N := F.biUnion fun g ↦
    (Finset.univ : Finset K).biUnion fun q ↦
      {φ ((g.right * q)⁻¹) g.left}
  obtain ⟨M⟩ := hN T ε hε
  refine ⟨{
    carrier := inducedSemidirectModel M.carrier K
    nonempty := by
      rw [card_inducedSemidirectModel]
      exact Nat.mul_pos M.nonempty (Fintype.card_pos_iff.mpr ⟨1⟩)
    map := inducedSemidirectPerm M.carrier φ M.map
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    rw [hammingDistance_inducedSemidirectPerm_mul _ _ _ _ _ M.nonempty]
    have hKpos : (0 : ℝ) < Fintype.card K := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
    apply (div_le_iff₀ hKpos).2
    calc
      ∑ q : K, hammingDistance M.carrier
          (M.map (φ (((g * h).right * q)⁻¹) (g * h).left))
          (M.map (φ ((g.right * (h.right * q))⁻¹) g.left) *
            M.map (φ ((h.right * q)⁻¹) h.left))
        ≤ ∑ _q : K, ε := by
          apply Finset.sum_le_sum
          intro q _
          rw [inducedSemidirect_label_mul]
          apply M.multiplicative
          · apply Finset.mem_biUnion.mpr
            refine ⟨g, hg, Finset.mem_biUnion.mpr ?_⟩
            exact ⟨h.right * q, Finset.mem_univ _, by simp⟩
          · apply Finset.mem_biUnion.mpr
            refine ⟨h, hh, Finset.mem_biUnion.mpr ?_⟩
            exact ⟨q, Finset.mem_univ _, by simp⟩
      _ = Fintype.card K * ε := by simp
      _ = ε * Fintype.card K := by ring
  · intro g hg h hh hne
    by_cases hright : g.right = h.right
    · rw [hammingDistance_inducedSemidirectPerm_of_right_eq
          M.carrier φ M.map hright M.nonempty]
      have hleft : g.left ≠ h.left := by
        intro hleft
        exact hne (SemidirectProduct.ext hleft hright)
      have hKpos : (0 : ℝ) < Fintype.card K := by
        exact_mod_cast Fintype.card_pos_iff.mpr ⟨1⟩
      apply (le_div_iff₀ hKpos).2
      calc
        (1 - ε) * Fintype.card K = ∑ _q : K, (1 - ε) := by
          simp
          ring
        _ ≤ ∑ q : K, hammingDistance M.carrier
            (M.map (φ ((g.right * q)⁻¹) g.left))
            (M.map (φ ((g.right * q)⁻¹) h.left)) := by
          apply Finset.sum_le_sum
          intro q _
          apply M.separated
          · apply Finset.mem_biUnion.mpr
            refine ⟨g, hg, Finset.mem_biUnion.mpr ?_⟩
            exact ⟨q, Finset.mem_univ _, by simp⟩
          · apply Finset.mem_biUnion.mpr
            refine ⟨h, hh, Finset.mem_biUnion.mpr ?_⟩
            exact ⟨q, Finset.mem_univ _, by simp [hright]⟩
          · exact fun heq ↦ hleft ((φ ((g.right * q)⁻¹)).injective heq)
    · rw [hammingDistance_inducedSemidirectPerm_of_right_ne
          M.carrier φ M.map hright M.nonempty]
      linarith

end GroupApproximation
