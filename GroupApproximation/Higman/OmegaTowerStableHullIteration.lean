import GroupApproximation.Higman.OmegaTowerOuterHull

/-!
# Finite-stage presentation of the Omega stable hull

The outer Omega subgroup meets its HNN base in a least edge-stable subgroup.
This file replaces that impredicative description by an explicit increasing
sequence: at each step, adjoin the forward and backward images of the part
which lies in the associated subgroup.  Every element of the stable hull is
therefore already present at a finite stage.  This is the induction principle
needed by the final arithmetic seam scan.
-/

namespace GroupApproximation
namespace Higman
namespace HNNDescent

variable {P : Type} [Group P] {A B : Subgroup P} (phi : A ≃* B)

/-- The forward edge image of the part of `Y` lying in `A`. -/
def forwardPart (Y : Subgroup P) : Subgroup P :=
  (Y.comap A.subtype).map (B.subtype.comp phi.toMonoidHom)

/-- The backward edge image of the part of `Y` lying in `B`. -/
def backwardPart (Y : Subgroup P) : Subgroup P :=
  (Y.comap B.subtype).map (A.subtype.comp phi.symm.toMonoidHom)

/-- One closure step under the two orientations of the HNN edge. -/
def stableStep (Y : Subgroup P) : Subgroup P :=
  Y ⊔ forwardPart phi Y ⊔ backwardPart phi Y

/-- The finite edge-closure stages starting from `Z`. -/
def stableStage (Z : Subgroup P) : ℕ → Subgroup P
  | 0 => Z
  | n + 1 => stableStep phi (stableStage Z n)

theorem le_stableStep (Y : Subgroup P) : Y ≤ stableStep phi Y := by
  exact le_sup_of_le_left (le_sup_left : Y ≤ Y ⊔ forwardPart phi Y)

theorem stableStage_mono (Z : Subgroup P) (n : ℕ) :
    stableStage phi Z n ≤ stableStage phi Z (n + 1) := by
  rw [stableStage]
  exact le_stableStep phi _

theorem stableStage_monotone (Z : Subgroup P) :
    Monotone (stableStage phi Z) :=
  monotone_nat_of_le_succ (stableStage_mono phi Z)

/-- The directed union of the finite edge-closure stages. -/
def finiteStableHull (Z : Subgroup P) : Subgroup P where
  carrier := {x | ∃ n, x ∈ stableStage phi Z n}
  one_mem' := ⟨0, Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨k, hy⟩
    refine ⟨max n k, Subgroup.mul_mem _
      (stableStage_monotone phi Z (Nat.le_max_left _ _) hx)
      (stableStage_monotone phi Z (Nat.le_max_right _ _) hy)⟩
  inv_mem' := by
    rintro x ⟨n, hx⟩
    exact ⟨n, Subgroup.inv_mem _ hx⟩

theorem stableStage_le_finiteStableHull (Z : Subgroup P) (n : ℕ) :
    stableStage phi Z n ≤ finiteStableHull phi Z := by
  exact fun _ hx => ⟨n, hx⟩

theorem le_finiteStableHull (Z : Subgroup P) : Z ≤ finiteStableHull phi Z := by
  simpa [stableStage] using stableStage_le_finiteStableHull phi Z 0

theorem forwardPart_mono {Y Y' : Subgroup P} (h : Y ≤ Y') :
    forwardPart phi Y ≤ forwardPart phi Y' := by
  exact Subgroup.map_mono (Subgroup.comap_mono h)

theorem backwardPart_mono {Y Y' : Subgroup P} (h : Y ≤ Y') :
    backwardPart phi Y ≤ backwardPart phi Y' := by
  exact Subgroup.map_mono (Subgroup.comap_mono h)

theorem stableStep_mono {Y Y' : Subgroup P} (h : Y ≤ Y') :
    stableStep phi Y ≤ stableStep phi Y' := by
  exact sup_le_sup (sup_le_sup h (forwardPart_mono phi h))
    (backwardPart_mono phi h)

theorem stableStage_le_of_le_stable {Z Y : Subgroup P}
    (hZY : Z ≤ Y) (hY : Stable phi Y) :
    ∀ n, stableStage phi Z n ≤ Y
  | 0 => hZY
  | n + 1 => by
      rw [stableStage]
      refine sup_le (sup_le (stableStage_le_of_le_stable hZY hY n) ?_) ?_
      · rintro y ⟨a, ha, rfl⟩
        exact hY.fwd a (stableStage_le_of_le_stable hZY hY n ha)
      · rintro y ⟨b, hb, rfl⟩
        exact hY.bwd b (stableStage_le_of_le_stable hZY hY n hb)

theorem finiteStableHull_le_of_le_stable {Z Y : Subgroup P}
    (hZY : Z ≤ Y) (hY : Stable phi Y) : finiteStableHull phi Z ≤ Y := by
  rintro x ⟨n, hx⟩
  exact stableStage_le_of_le_stable phi hZY hY n hx

theorem stable_finiteStableHull (Z : Subgroup P) :
    Stable phi (finiteStableHull phi Z) := by
  constructor
  · rintro a ha
    obtain ⟨n, ha⟩ := ha
    apply stableStage_le_finiteStableHull phi Z (n + 1)
    exact Subgroup.mem_sup_left
      (Subgroup.mem_sup_right ⟨a, ha, rfl⟩)
  · rintro b hb
    obtain ⟨n, hb⟩ := hb
    apply stableStage_le_finiteStableHull phi Z (n + 1)
    exact Subgroup.mem_sup_right ⟨b, hb, rfl⟩

/-- **Finite-stage stable-hull theorem.**  The least stable subgroup is the
union of the explicit finite closure stages. -/
theorem stableHull_eq_finiteStableHull (Z : Subgroup P) :
    stableHull phi Z = finiteStableHull phi Z := by
  apply le_antisymm
  · exact stableHull_le phi (le_finiteStableHull phi Z)
      (stable_finiteStableHull phi Z)
  · exact finiteStableHull_le_of_le_stable phi (le_stableHull phi Z)
      (stable_stableHull phi Z)

/-- Every stable-hull element occurs at one finite edge-closure stage. -/
theorem mem_stableHull_iff_exists_stage {Z : Subgroup P} {x : P} :
    x ∈ stableHull phi Z ↔ ∃ n, x ∈ stableStage phi Z n := by
  rw [stableHull_eq_finiteStableHull]
  rfl

end HNNDescent

namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq

/-- The coded subgroup attached to `omegaOp` is invariant under the
`m`-fold shift.  Both inclusions are proved on literal conjugate-basis
generators; the reverse inclusion uses `unshift`. -/
theorem map_shiftEquiv_pow_ASub_omega (m : ℕ) (B : Set E) :
    (ASub (omegaOp m B)).map
        ((shiftEquiv : MulAut F₃) ^ m).toMonoidHom =
      ASub (omegaOp m B) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    unfold ASub at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨f, hf, rfl⟩ := hx
        apply Subgroup.subset_closure
        refine ⟨shiftPow m f, (mem_omegaOp_shiftPow m B f).mpr hf, ?_⟩
        change aElt (shiftPow m f) =
          ((shiftEquiv : MulAut F₃) ^ m) (aElt f)
        rw [shiftEquiv_pow_apply, shiftAut_iterate_aElt]
    | one => simp
    | mul x y _ _ hx hy => simpa only [map_mul] using Subgroup.mul_mem _ hx hy
    | inv x _ hx => simpa only [map_inv] using Subgroup.inv_mem _ hx
  · unfold ASub
    rw [Subgroup.closure_le]
    rintro x ⟨f, hf, rfl⟩
    have hun : unshift m f ∈ omegaOp m B := by
      apply (mem_omegaOp_shiftPow m B (unshift m f)).mp
      rwa [shiftPow_unshift]
    refine ⟨aElt (unshift m f), Subgroup.subset_closure ⟨_, hun, rfl⟩, ?_⟩
    change ((shiftEquiv : MulAut F₃) ^ m) (aElt (unshift m f)) = aElt f
    rw [shiftEquiv_pow_apply, shiftAut_iterate_aElt, shiftPow_unshift]

/-- The copy of `A_(omegaOp m B)` in the second-stage base is stable under
both orientations of the outer HNN edge. -/
theorem stable_map_slimPiF3Hom_ASub_omega (m : ℕ) (B : Set E) :
    HNNDescent.Stable (slimShiftRangeEquiv m)
      ((ASub (omegaOp m B)).map (slimPiF3Hom m)) := by
  constructor
  · rintro a ha
    obtain ⟨x, hx, hxa⟩ := ha
    have hshift : ((shiftEquiv : MulAut F₃) ^ m) x ∈ ASub (omegaOp m B) := by
      rw [← map_shiftEquiv_pow_ASub_omega m B]
      exact ⟨x, hx, rfl⟩
    refine ⟨((shiftEquiv : MulAut F₃) ^ m) x, hshift, ?_⟩
    have haa :
        (⟨slimPiF3Hom m x, ⟨x, rfl⟩⟩ : (slimPiF3Hom m).range) = a :=
      Subtype.ext hxa
    have hs := slimShiftRangeEquiv_apply m x
    simpa [haa] using hs.symm
  · rintro b hb
    obtain ⟨x, hx, hxb⟩ := hb
    let y : F₃ := (((shiftEquiv : MulAut F₃) ^ m).symm x)
    have hy : y ∈ ASub (omegaOp m B) := by
      rw [← map_shiftEquiv_pow_ASub_omega m B] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzy : z = y := by
        apply ((shiftEquiv : MulAut F₃) ^ m).injective
        simpa [y] using hzx
      rwa [hzy] at hz
    refine ⟨y, hy, ?_⟩
    have hby :
        slimShiftRangeEquiv m
          ⟨slimPiF3Hom m y, ⟨y, rfl⟩⟩ = b := by
      apply Subtype.ext
      rw [slimShiftRangeEquiv_apply]
      simpa [y] using hxb
    have hi := congrArg (slimShiftRangeEquiv m).symm hby
    simpa only [MulEquiv.symm_apply_apply] using congrArg Subtype.val hi

end Omega
end Higman
end GroupApproximation
