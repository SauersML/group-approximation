import GroupApproximation.Higman.CentralHNNFreeLabelRightAction

/-!
# Affine form of the central-HNN free-label action

The free-label lift acts at an arbitrary base coordinate by applying the
right-coset translation determined by that coordinate, then multiplying the
translated free word on the left.  This is the coordinate formula needed to
scan subgroups generated simultaneously by base words and stable conjugates.
-/

namespace GroupApproximation
namespace Higman
namespace CentralHNNFreeLabel

open HNNExtension

variable {G : Type} [Group G] (M : Subgroup G)

@[simp] theorem rightLabel_one
    (d : HNNExtension.NormalWord.TransversalPair G M M) (q : Label M d) :
    rightLabel (M := M) d 1 q = q := by
  unfold rightLabel
  simpa only [mul_one] using label_self M d q

/-- Successive right translations compose in the same order as multiplication
of their base coordinates. -/
theorem rightLabel_comp
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (g h : G) (q : Label M d) :
    rightLabel (M := M) d g (rightLabel (M := M) d h q) =
      rightLabel (M := M) d (h * g) q := by
  have hleft := stableConj_rightLabel (M := M) d g
    (rightLabel (M := M) d h q)
  have hinner := stableConj_rightLabel (M := M) d h q
  have hright := stableConj_rightLabel (M := M) d (h * g) q
  have heq :
      stableConj M d
          (rightLabel (M := M) d g (rightLabel (M := M) d h q)) =
        stableConj M d (rightLabel (M := M) d (h * g) q) := by
    rw [← hleft, ← hright, ← hinner]
    simp only [map_mul, map_inv]
    group
  have haction := congrArg (action M d) heq
  have happ := DFunLike.congr_fun haction
    ((1 : G), (1 : FreeGroup (Label M d)))
  rw [action_stableConj_apply_one, action_stableConj_apply_one] at happ
  exact FreeGroup.of_injective (congrArg Prod.snd happ)

/-- Translating the label of a concrete base element gives the label of its
right product. -/
theorem rightLabel_labelOf
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g s : G) :
    rightLabel (M := M) d g (((d.compl (1 : ℤˣ)).equiv s).2) =
      ((d.compl (1 : ℤˣ)).equiv (s * g)).2 := by
  have hright := stableConj_rightLabel (M := M) d g
    (((d.compl (1 : ℤˣ)).equiv s).2)
  have hs := stableConj_eq_conj_of_label_eq M d
    (((d.compl (1 : ℤˣ)).equiv s).2) s rfl
  have hsg := stableConj_eq_conj_of_label_eq M d
    (((d.compl (1 : ℤˣ)).equiv (s * g)).2) (s * g) rfl
  have heq :
      stableConj M d
          (rightLabel (M := M) d g (((d.compl (1 : ℤˣ)).equiv s).2)) =
        stableConj M d (((d.compl (1 : ℤˣ)).equiv (s * g)).2) := by
    rw [← hright, hs, hsg]
    simp only [map_mul, map_inv]
    group
  have haction := congrArg (action M d) heq
  have happ := DFunLike.congr_fun haction
    ((1 : G), (1 : FreeGroup (Label M d)))
  rw [action_stableConj_apply_one, action_stableConj_apply_one] at happ
  exact FreeGroup.of_injective (congrArg Prod.snd happ)

/-- Right translation by an element of `S` permutes exactly the coset labels
met by `S`. -/
theorem image_rightLabel_labelSet
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (S : Subgroup G) {g : G} (hg : g ∈ S) :
    rightLabel (M := M) d g '' labelSet M d S = labelSet M d S := by
  ext q
  constructor
  · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
    rw [rightLabel_labelOf]
    exact ⟨s * g, S.mul_mem hs hg, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((d.compl (1 : ℤˣ)).equiv (s * g⁻¹)).2, ?_, ?_⟩
    · exact ⟨s * g⁻¹, S.mul_mem hs (S.inv_mem hg), rfl⟩
    · rw [rightLabel_labelOf]
      congr 2
      group

/-- The corresponding alphabet maps compose as free-group homomorphisms. -/
theorem freeGroupMap_rightLabel_comp
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g h : G) :
    (FreeGroup.map (rightLabel (M := M) d g)).comp
        (FreeGroup.map (rightLabel (M := M) d h)) =
      FreeGroup.map (rightLabel (M := M) d (h * g)) := by
  refine FreeGroup.ext_hom _ _ fun q => ?_
  simp only [MonoidHom.comp_apply, FreeGroup.map.of]
  rw [rightLabel_comp]

/-- Evaluation of a free stable-conjugate word at an arbitrary base point.
The base point right-translates every free label before evaluation. -/
theorem action_stableConjLift_apply_right
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (v : FreeGroup (Label M d)) (x : G)
    (w : FreeGroup (Label M d)) :
    action M d (stableConjLift M d v) (x, w) =
      (x, FreeGroup.map (rightLabel (M := M) d x) v * w) := by
  have hconj := stableConjLift_rightLabel (M := M) d x v
  have hmul :
      stableConjLift M d v * of x =
        of x * stableConjLift M d
          (FreeGroup.map (rightLabel (M := M) d x) v) := by
    calc
      stableConjLift M d v * of x =
          of x * (of x⁻¹ * stableConjLift M d v * of x) := by
            rw [map_inv]
            group
      _ = of x * stableConjLift M d
          (FreeGroup.map (rightLabel (M := M) d x) v) := by rw [hconj]
  have haction := congrArg (action M d) hmul
  have happ := DFunLike.congr_fun haction
    ((1 : G), w)
  simpa only [map_mul, Equiv.Perm.mul_apply, action_of, basePerm_apply,
    one_mul, mul_one, action_stableConjLift_apply] using happ

/-- The free coordinate read by the faithful action at its distinguished
point.  It is defined for every element, not only for the retraction kernel. -/
noncomputable def freeCoord
    (d : HNNExtension.NormalWord.TransversalPair G M M) (z : CentHNN M) :
    FreeGroup (Label M d) :=
  (action M d z ((1 : G), (1 : FreeGroup (Label M d)))).2

@[simp] theorem freeCoord_one
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    freeCoord M d 1 = 1 := by
  simp [freeCoord]

@[simp] theorem freeCoord_of
    (d : HNNExtension.NormalWord.TransversalPair G M M) (g : G) :
    freeCoord M d (of g) = 1 := by
  simp [freeCoord]

@[simp] theorem freeCoord_t
    (d : HNNExtension.NormalWord.TransversalPair G M M) :
    freeCoord M d (t : CentHNN M) =
      FreeGroup.of (((d.compl (1 : ℤˣ)).equiv 1).2) := by
  rfl

@[simp] theorem freeCoord_stableConjLift
    (d : HNNExtension.NormalWord.TransversalPair G M M)
    (w : FreeGroup (Label M d)) :
    freeCoord M d (stableConjLift M d w) = w := by
  simpa [freeCoord] using congrArg Prod.snd
    (action_stableConjLift_apply_one M d w)

/-- At the distinguished point the two action coordinates are exactly the
base return and the free coordinate. -/
theorem action_apply_one_eq_baseRet_freeCoord
    (d : HNNExtension.NormalWord.TransversalPair G M M) (z : CentHNN M) :
    action M d z ((1 : G), (1 : FreeGroup (Label M d))) =
      (baseRet M z, freeCoord M d z) := by
  apply Prod.ext
  · simpa only [mul_one] using action_fst_apply M d z 1 1
  · rfl

/-- Every central-HNN element factors uniquely into its base return followed
by its free stable-conjugate coordinate. -/
theorem eq_of_baseRet_mul_stableConjLift_freeCoord
    (d : HNNExtension.NormalWord.TransversalPair G M M) (z : CentHNN M) :
    z = of (baseRet M z) * stableConjLift M d (freeCoord M d z) := by
  apply eq_of_action_apply_eq M d
  rw [action_apply_one_eq_baseRet_freeCoord, map_mul,
    Equiv.Perm.mul_apply, action_stableConjLift_apply_one, action_of,
    basePerm_apply, mul_one]

/-- Full affine action formula for an arbitrary central-HNN element. -/
theorem action_apply_affine
    (d : HNNExtension.NormalWord.TransversalPair G M M) (z : CentHNN M)
    (x : G) (w : FreeGroup (Label M d)) :
    action M d z (x, w) =
      (baseRet M z * x,
        FreeGroup.map (rightLabel (M := M) d x) (freeCoord M d z) * w) := by
  conv_lhs => rw [eq_of_baseRet_mul_stableConjLift_freeCoord M d z]
  rw [map_mul,
    Equiv.Perm.mul_apply, action_stableConjLift_apply_right, action_of,
    basePerm_apply]

/-- Multiplication is the semidirect-product rule: the free coordinate of the
left factor is right-translated by the base return of the right factor. -/
theorem freeCoord_mul
    (d : HNNExtension.NormalWord.TransversalPair G M M) (x y : CentHNN M) :
    freeCoord M d (x * y) =
      FreeGroup.map (rightLabel (M := M) d (baseRet M y))
          (freeCoord M d x) * freeCoord M d y := by
  unfold freeCoord
  rw [map_mul, Equiv.Perm.mul_apply,
    action_apply_one_eq_baseRet_freeCoord,
    action_apply_affine]
  rfl

/-- Inversion in affine coordinates. -/
theorem freeCoord_inv
    (d : HNNExtension.NormalWord.TransversalPair G M M) (z : CentHNN M) :
    freeCoord M d z⁻¹ =
      (FreeGroup.map (rightLabel (M := M) d (baseRet M z⁻¹))
        (freeCoord M d z))⁻¹ := by
  have hmul := freeCoord_mul M d z z⁻¹
  let u := FreeGroup.map
    (rightLabel (M := M) d (baseRet M z⁻¹)) (freeCoord M d z)
  have hprod : u * freeCoord M d z⁻¹ = 1 := by
    simpa only [mul_inv_cancel, freeCoord_one] using hmul.symm
  calc
    freeCoord M d z⁻¹ = u⁻¹ * (u * freeCoord M d z⁻¹) := by group
    _ = u⁻¹ := by rw [hprod, mul_one]

end CentralHNNFreeLabel
end Higman
end GroupApproximation
