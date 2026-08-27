import GroupApproximation.Higman.BridgePresentation
import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridge

/-!
# An effective presentation of the printed, two-sided bridge

The effective HNN bridge in `Higman.BridgePresentation` uses only the
one-sided family `x⁻ⁿ y xⁿ`.  The recognition manuscript needs the genuinely
different two-sided family `xⁱ y x⁻ⁱ`, because its trivial specialization is
the subgroup of `F₂ × F₂` used in the positive branch.  This file transports
the whole two-sided edge isomorphism to the enumerable presentation of the
base `C * F₂`.

`edgeIndex` enumerates `ℤ` as `0,1,-1,2,-2,...`.  Consequently the source and
target word families below generate exactly `Ysub` and `CYsub`; no one-sided
bridge is substituted for the printed group.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge
namespace Presentation

open GroupApproximation.Higman
open GroupApproximation.Higman.HNNEmb
namespace BP
export GroupApproximation.Higman.BridgePresentation
  (baseEquiv baseRels baseEquiv_of_zero baseEquiv_of_one
    baseEquiv_of_add_two optionNatEquiv)
end BP

/-! ## The two-sided edge family on a natural-number index -/

/-- The computable enumeration `0,1,-1,2,-2,...` of all integers. -/
def edgeIndex (n : ℕ) : ℤ :=
  if n % 2 = 0 then -((n / 2 : ℕ) : ℤ) else ((n / 2 + 1 : ℕ) : ℤ)

theorem edgeIndex_even (k : ℕ) : edgeIndex (2 * k) = -(k : ℤ) := by
  rw [edgeIndex, if_pos (by omega)]
  congr 1
  omega

theorem edgeIndex_odd (k : ℕ) : edgeIndex (2 * k + 1) = (k + 1 : ℕ) := by
  rw [edgeIndex, if_neg (by omega)]
  congr 1
  omega

theorem edgeIndex_surjective : Function.Surjective edgeIndex := by
  intro z
  cases z with
  | ofNat k =>
      cases k with
      | zero => exact ⟨0, by simp [edgeIndex]⟩
      | succ k => exact ⟨2 * k + 1, by simpa using edgeIndex_odd k⟩
  | negSucc k =>
      refine ⟨2 * (k + 1), ?_⟩
      change edgeIndex (2 * (k + 1)) = -((k + 1 : ℕ) : ℤ)
      exact edgeIndex_even (k + 1)

/-- The word `xⁱ y x⁻ⁱ` in the numbered base presentation, with `i` supplied
by `edgeIndex`. -/
def srcWord (n : ℕ) : FreeGroup ℕ :=
  FreeGroup.of 0 ^ edgeIndex n * FreeGroup.of 1 *
    FreeGroup.of 0 ^ (-edgeIndex n)

/-- The word `cᵢ xⁱ y x⁻ⁱ`; the normalized family has `cᵢ=1` for `i≤0`.
In the odd branch `edgeIndex (2k+1)=k+1`, so `cᵢ` is base generator `k+2`.
-/
def tgtWord (n : ℕ) : FreeGroup ℕ :=
  if n % 2 = 0 then srcWord n else FreeGroup.of (n / 2 + 2) * srcWord n

theorem baseEquiv_srcWord {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (n : ℕ) :
    BP.baseEquiv g hspan (PresentedGroup.mk (BP.baseRels g) (srcWord n)) =
      yBase C (edgeIndex n) := by
  unfold srcWord yBase
  simp only [map_mul, map_zpow]
  change (BP.baseEquiv g hspan (PresentedGroup.of 0)) ^ edgeIndex n *
      BP.baseEquiv g hspan (PresentedGroup.of 1) *
      (BP.baseEquiv g hspan (PresentedGroup.of 0)) ^ (-edgeIndex n) = _
  rw [BP.baseEquiv_of_zero, BP.baseEquiv_of_one]

theorem baseEquiv_tgtWord {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (n : ℕ) :
    BP.baseEquiv g hspan (PresentedGroup.mk (BP.baseRels g) (tgtWord n)) =
      cyBase (seq g) (edgeIndex n) := by
  by_cases hn : n % 2 = 0
  · have hi : edgeIndex n ≤ 0 := by
      rw [edgeIndex, if_pos hn]
      omega
    rw [tgtWord, if_pos hn, baseEquiv_srcWord, cyBase, seq_nonpos g hi,
      map_one, one_mul]
  · have hnodd : n % 2 = 1 := by omega
    have hindex : edgeIndex n = ((n / 2 + 1 : ℕ) : ℤ) := by
      rw [edgeIndex, if_neg hn]
    rw [tgtWord, if_neg hn]
    simp only [map_mul]
    change BP.baseEquiv g hspan (PresentedGroup.of (n / 2 + 2)) *
        BP.baseEquiv g hspan
          (PresentedGroup.mk (BP.baseRels g) (srcWord n)) = _
    rw [BP.baseEquiv_of_add_two, baseEquiv_srcWord, cyBase, hindex, seq_pos]

theorem baseEquiv_symm_yBase {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (n : ℕ) :
    (BP.baseEquiv g hspan).symm (yBase C (edgeIndex n)) =
      HNNPresentation.srcGen (BP.baseRels g) srcWord n := by
  rw [← baseEquiv_srcWord g hspan n, MulEquiv.symm_apply_apply]
  rfl

theorem baseEquiv_symm_cyBase {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (n : ℕ) :
    (BP.baseEquiv g hspan).symm (cyBase (seq g) (edgeIndex n)) =
      HNNPresentation.tgtGen (BP.baseRels g) tgtWord n := by
  rw [← baseEquiv_tgtWord g hspan n, MulEquiv.symm_apply_apply]
  rfl

/-! ## Transport of the two associated subgroups -/

theorem map_Ysub {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    (Ysub C).map (BP.baseEquiv g hspan).symm.toMonoidHom =
      HNNPresentation.srcSub (BP.baseRels g) srcWord := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨W, rfl⟩ := hx
    refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
    · rw [map_one, map_one]
      exact Subgroup.one_mem _
    · intro i
      obtain ⟨n, hn⟩ := edgeIndex_surjective i
      subst i
      change (BP.baseEquiv g hspan).symm
          (yBaseHom C (FreeGroup.of (edgeIndex n))) ∈ _
      rw [yBaseHom_of, baseEquiv_symm_yBase]
      exact HNNPresentation.srcGen_mem (BP.baseRels g) srcWord n
    · intro W hW
      rw [map_inv, map_inv]
      exact Subgroup.inv_mem _ hW
    · intro U V hU hV
      rw [map_mul, map_mul]
      exact Subgroup.mul_mem _ hU hV
  · rw [HNNPresentation.srcSub, Subgroup.closure_le]
    rintro y ⟨n, rfl⟩
    refine ⟨yBase C (edgeIndex n), yBase_mem_Ysub (edgeIndex n), ?_⟩
    exact baseEquiv_symm_yBase g hspan n

theorem map_CYsub {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    (CYsub (seq g)).map (BP.baseEquiv g hspan).symm.toMonoidHom =
      HNNPresentation.tgtSub (BP.baseRels g) tgtWord := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨W, rfl⟩ := hx
    refine FreeGroup.induction_on W ?_ ?_ ?_ ?_
    · rw [map_one, map_one]
      exact Subgroup.one_mem _
    · intro i
      obtain ⟨n, hn⟩ := edgeIndex_surjective i
      subst i
      change (BP.baseEquiv g hspan).symm
          (cyBaseHom (seq g) (FreeGroup.of (edgeIndex n))) ∈ _
      rw [cyBaseHom_of, baseEquiv_symm_cyBase]
      exact HNNPresentation.tgtGen_mem (BP.baseRels g) tgtWord n
    · intro W hW
      rw [map_inv, map_inv]
      exact Subgroup.inv_mem _ hW
    · intro U V hU hV
      rw [map_mul, map_mul]
      exact Subgroup.mul_mem _ hU hV
  · rw [HNNPresentation.tgtSub, Subgroup.closure_le]
    rintro y ⟨n, rfl⟩
    refine ⟨cyBase (seq g) (edgeIndex n), cyBase_mem_CYsub _ _, ?_⟩
    exact baseEquiv_symm_cyBase g hspan n

theorem mem_Ysub_iff {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (x : Higman.HNNEmb.P C) :
    x ∈ Ysub C ↔ (BP.baseEquiv g hspan).symm x ∈
      HNNPresentation.srcSub (BP.baseRels g) srcWord := by
  rw [← map_Ysub g hspan, Subgroup.mem_map_equiv,
    MulEquiv.symm_symm, MulEquiv.apply_symm_apply]

/-- The printed edge isomorphism transported to the presented base. -/
noncomputable def presPhi {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    HNNPresentation.srcSub (BP.baseRels g) srcWord ≃*
      HNNPresentation.tgtSub (BP.baseRels g) tgtWord :=
  (((MulEquiv.subgroupCongr (map_Ysub g hspan)).symm.trans
      ((BP.baseEquiv g hspan).symm.subgroupMap (Ysub C)).symm).trans
      (bridgePsi (seq g))).trans
    (((BP.baseEquiv g hspan).symm.subgroupMap (CYsub (seq g))).trans
      (MulEquiv.subgroupCongr (map_CYsub g hspan)))

theorem presPhi_intertwines {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    HNNCongr.Intertwines (bridgePsi (seq g)) (presPhi g hspan)
      (BP.baseEquiv g hspan).symm (mem_Ysub_iff g hspan) := by
  intro a ha
  have hsub : (⟨BP.baseEquiv g hspan ((BP.baseEquiv g hspan).symm a), by
        rw [MulEquiv.apply_symm_apply]
        exact ha⟩ : Ysub C) = ⟨a, ha⟩ :=
    Subtype.ext (MulEquiv.apply_symm_apply _ a)
  show (BP.baseEquiv g hspan).symm
      (((bridgePsi (seq g))
        ⟨BP.baseEquiv g hspan ((BP.baseEquiv g hspan).symm a), _⟩ :
          CYsub (seq g)) : Higman.HNNEmb.P C) =
    (BP.baseEquiv g hspan).symm
      (((bridgePsi (seq g)) ⟨a, ha⟩ : CYsub (seq g)) : Higman.HNNEmb.P C)
  rw [hsub]

theorem presPhi_gen {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (n : ℕ) :
    ((presPhi g hspan
        ⟨HNNPresentation.srcGen (BP.baseRels g) srcWord n,
          HNNPresentation.srcGen_mem (BP.baseRels g) srcWord n⟩ :
          HNNPresentation.tgtSub (BP.baseRels g) tgtWord) :
        PresentedGroup (BP.baseRels g)) =
      HNNPresentation.tgtGen (BP.baseRels g) tgtWord n := by
  have hsrc : HNNPresentation.srcGen (BP.baseRels g) srcWord n =
      (BP.baseEquiv g hspan).symm (yBase C (edgeIndex n)) :=
    (baseEquiv_symm_yBase g hspan n).symm
  have hmem : yBase C (edgeIndex n) ∈ Ysub C := yBase_mem_Ysub _
  have hsub :
      (⟨HNNPresentation.srcGen (BP.baseRels g) srcWord n,
          HNNPresentation.srcGen_mem (BP.baseRels g) srcWord n⟩ :
        HNNPresentation.srcSub (BP.baseRels g) srcWord) =
      ⟨(BP.baseEquiv g hspan).symm (yBase C (edgeIndex n)),
        (mem_Ysub_iff g hspan _).1 hmem⟩ := Subtype.ext hsrc
  rw [hsub, presPhi_intertwines g hspan _ hmem]
  have hW : yBaseHom C (FreeGroup.of (edgeIndex n)) ∈ Ysub C :=
    ⟨FreeGroup.of (edgeIndex n), rfl⟩
  have harg : (⟨yBase C (edgeIndex n), hmem⟩ : Ysub C) =
      ⟨yBaseHom C (FreeGroup.of (edgeIndex n)), hW⟩ :=
    Subtype.ext (yBaseHom_of (edgeIndex n)).symm
  rw [harg, bridgePsi_apply, cyBaseHom_of]
  exact baseEquiv_symm_cyBase g hspan n

/-! ## The literal numbered presentation -/

def hnnNumberedRels {C : Type} [Group C] (g : ℕ → C) : Set (FreeGroup ℕ) :=
  PresentedGroupRelabel.relabelRels (BP.optionNatEquiv : Option ℕ → ℕ)
    (HNNPresentation.hnnRels (BP.baseRels g) srcWord tgtWord)

/-- The printed two-sided bridge is the literal HNN presentation above. -/
noncomputable def extEquivNumbered {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    BGroup (seq g) ≃* PresentedGroup (hnnNumberedRels g) :=
  ((HNNCongr.congrEquiv (bridgePsi (seq g)) (presPhi g hspan)
      (BP.baseEquiv g hspan).symm (mem_Ysub_iff g hspan)
      (presPhi_intertwines g hspan)).trans
    (HNNPresentation.equivPres (BP.baseRels g) srcWord tgtWord (presPhi g hspan)
      (presPhi_gen g hspan)).symm).trans
    (PresentedGroupRelabel.congrEquiv BP.optionNatEquiv
      (HNNPresentation.hnnRels (BP.baseRels g) srcWord tgtWord))

end Presentation
end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
