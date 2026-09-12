import GroupApproximation.Manuscript.MFRecognition.ThreeGeneratorBridgeEffectivity

/-!
# The recursive three-generator presentation of the printed bridge

The preceding files identify the printed two-sided HNN extension with a
presented group whose relators admit a primitive-recursive search.  Here we
track the three manuscript generators through that equivalence and pull the
canonical recursively enumerable word problem back to `qC`.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Bridge
namespace Effectivity

open GroupApproximation.Higman
open GroupApproximation.Higman.HNNEmb
open Presentation
namespace BP
export GroupApproximation.Higman.BridgePresentation
  (baseRels optionNatEquiv cycle extEquivNumbered_t extEquivNumbered_x
    extEquivNumbered_y primrec_cycle)
end BP

/-! ## The three generators through the literal equivalence -/

theorem extEquivNumbered_t {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Presentation.extEquivNumbered g hspan
      (HNNExtension.t : BGroup (seq g)) = PresentedGroup.of 0 := by
  show PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      ((HNNPresentation.equivPres (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)).symm
        (HNNCongr.congrEquiv (bridgePsi (seq g)) (Presentation.presPhi g hspan)
          (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
          (Presentation.mem_Ysub_iff g hspan)
          (Presentation.presPhi_intertwines g hspan) HNNExtension.t)) = _
  rw [show HNNCongr.congrEquiv (bridgePsi (seq g))
      (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan)
      (HNNExtension.t : BGroup (seq g)) = HNNExtension.t from
    HNNCongr.congrHom_t (bridgePsi (seq g)) (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan)]
  change PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      (HNNPresentation.bwd (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)
        HNNExtension.t) = _
  rw [HNNPresentation.bwd, HNNExtension.lift_t]
  exact PresentedGroupRelabel.relabelHom_of BP.optionNatEquiv _ none

theorem extEquivNumbered_x {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Presentation.extEquivNumbered g hspan
      (HNNExtension.of (xg : Higman.HNNEmb.P C)) = PresentedGroup.of 1 := by
  show PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      ((HNNPresentation.equivPres (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)).symm
        (HNNCongr.congrEquiv (bridgePsi (seq g)) (Presentation.presPhi g hspan)
          (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
          (Presentation.mem_Ysub_iff g hspan)
          (Presentation.presPhi_intertwines g hspan)
          (HNNExtension.of (xg : Higman.HNNEmb.P C)))) = _
  rw [show HNNCongr.congrEquiv (bridgePsi (seq g))
      (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan)
      (HNNExtension.of (xg : Higman.HNNEmb.P C)) =
        HNNExtension.of
          ((GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm xg) from
    HNNCongr.congrHom_of (bridgePsi (seq g)) (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan) xg]
  change PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      (HNNPresentation.bwd (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)
        (HNNExtension.of
          ((GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm xg))) = _
  rw [HNNPresentation.bwd, HNNExtension.lift_of]
  have hx :
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm xg =
        (PresentedGroup.of 0 : PresentedGroup (BP.baseRels g)) := by
    rw [MulEquiv.symm_apply_eq]
    exact (GroupApproximation.Higman.BridgePresentation.baseEquiv_of_zero g hspan).symm
  rw [hx, HNNPresentation.bwdBase, PresentedGroup.toGroup.of]
  exact PresentedGroupRelabel.relabelHom_of BP.optionNatEquiv _ (some 0)

theorem extEquivNumbered_y {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) :
    Presentation.extEquivNumbered g hspan
      (HNNExtension.of (yg : Higman.HNNEmb.P C)) = PresentedGroup.of 2 := by
  show PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      ((HNNPresentation.equivPres (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)).symm
        (HNNCongr.congrEquiv (bridgePsi (seq g)) (Presentation.presPhi g hspan)
          (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
          (Presentation.mem_Ysub_iff g hspan)
          (Presentation.presPhi_intertwines g hspan)
          (HNNExtension.of (yg : Higman.HNNEmb.P C)))) = _
  rw [show HNNCongr.congrEquiv (bridgePsi (seq g))
      (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan)
      (HNNExtension.of (yg : Higman.HNNEmb.P C)) =
        HNNExtension.of
          ((GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm yg) from
    HNNCongr.congrHom_of (bridgePsi (seq g)) (Presentation.presPhi g hspan)
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm
      (Presentation.mem_Ysub_iff g hspan)
      (Presentation.presPhi_intertwines g hspan) yg]
  change PresentedGroupRelabel.congrEquiv BP.optionNatEquiv _
      (HNNPresentation.bwd (BP.baseRels g) srcWord tgtWord
        (Presentation.presPhi g hspan) (Presentation.presPhi_gen g hspan)
        (HNNExtension.of
          ((GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm yg))) = _
  rw [HNNPresentation.bwd, HNNExtension.lift_of]
  have hy :
      (GroupApproximation.Higman.BridgePresentation.baseEquiv g hspan).symm yg =
        (PresentedGroup.of 1 : PresentedGroup (BP.baseRels g)) := by
    rw [MulEquiv.symm_apply_eq]
    exact (GroupApproximation.Higman.BridgePresentation.baseEquiv_of_one g hspan).symm
  rw [hy, HNNPresentation.bwdBase, PresentedGroup.toGroup.of]
  exact PresentedGroupRelabel.relabelHom_of BP.optionNatEquiv _ (some 1)

theorem extEquivCoded_gen3 {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (j : Fin 3) :
    extEquivCoded g hspan (Bridge.gen3 (seq g) j) =
      PresentedGroup.of ((j.1 + 1) % 3) := by
  fin_cases j <;>
    simp [extEquivCoded, Bridge.gen3, extEquivNumbered_x,
      extEquivNumbered_y, extEquivNumbered_t, BP.normalClosureEquiv_of]

theorem qC_to_coded {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤) (v : RawWord) :
    extEquivCoded g hspan (qC (seq g) (rawToFree 2 v)) =
      evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup (codedRels g)))
        (relabel (fun k ↦ (k + 1) % 3) v) := by
  unfold qC
  rw [BridgeWP.lift_rawToFree]
  change extEquivCoded g hspan
      (evalRaw (fun k : ℕ ↦
        Bridge.gen3 (seq g) ⟨k % 3, Nat.mod_lt _ (by omega)⟩) v) = _
  change (extEquivCoded g hspan).toMonoidHom
      (evalRaw (fun k : ℕ ↦
        Bridge.gen3 (seq g) ⟨k % 3, Nat.mod_lt _ (by omega)⟩) v) = _
  rw [map_evalRaw, evalRaw_relabel]
  refine congrArg (fun f : ℕ → PresentedGroup (codedRels g) ↦ evalRaw f v) ?_
  funext k
  change extEquivCoded g hspan
      (Bridge.gen3 (seq g) ⟨k % 3, Nat.mod_lt _ (by omega)⟩) =
        PresentedGroup.of ((k + 1) % 3)
  rw [extEquivCoded_gen3]
  congr 1
  simp [Nat.add_mod]

/-! ## The recursively enumerable three-letter word problem -/

theorem inv_mem_codedRels {C : Type} [Group C] (g : ℕ → C)
    {z : FreeGroup ℕ} (hz : z ∈ codedRels g) : z⁻¹ ∈ codedRels g := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact ⟨x⁻¹, inv_mem_relSet g hx, map_inv _ _⟩

theorem symmetrize_codedRels {C : Type} [Group C] (g : ℕ → C) :
    symmetrize (codedRels g) = codedRels g := by
  refine Set.union_eq_self_of_subset_right ?_
  rintro _ ⟨z, hz, rfl⟩
  exact inv_mem_codedRels g hz

theorem search_codedRels {C : Type} [Group C] (g : ℕ → C)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    ∃ f : RawWord → ℕ → Bool, Primrec₂ f ∧
      ∀ v : RawWord, freeEval v ∈ symmetrize (codedRels g) ↔
        ∃ n, f v n = true := by
  obtain ⟨f, hf, hspec⟩ := search_relSet g hre
  obtain ⟨F, hF, hFspec⟩ := search_image BP.primrec_cycle hf hspec
  obtain ⟨F', hF', hF'spec⟩ := search_reindex F hF
  refine ⟨F', hF', fun v ↦ ?_⟩
  rw [symmetrize_codedRels]
  exact (hFspec v).trans (hF'spec v)

theorem rePred_qC_of_spans {C : Type} [Group C] (g : ℕ → C)
    (hspan : Subgroup.closure (Set.range g) = ⊤)
    (hre : REPred fun w : RawWord ↦ evalRaw g w = 1) :
    REPred fun v : RawWord ↦ qC (seq g) (rawToFree 2 v) = 1 := by
  obtain ⟨f, hf, hspec⟩ := search_codedRels g hre
  have hcanonical : REPred fun w : RawWord ↦
      evalRaw (fun k ↦ (PresentedGroup.of k : PresentedGroup (codedRels g))) w = 1 :=
    rePred_wordProblem_of_relators f _ (codedRels g)
      (evalRaw_presentedGroup_eq_one_iff (codedRels g)) hf hspec
  have hrotate : Computable fun v : RawWord ↦ relabel (fun k ↦ (k + 1) % 3) v :=
    (primrec_relabel
      (Primrec.nat_mod.comp
        (Primrec.nat_add.comp Primrec.id (Primrec.const 1))
        (Primrec.const 3))).to_comp
  refine (BridgeWP.rePred_comp hcanonical hrotate).of_eq fun v ↦ ?_
  rw [← qC_to_coded g hspan]
  exact (extEquivCoded g hspan).map_eq_one_iff

end Effectivity

/-! ## The manuscript endpoint -/

/-- **`lem:bridge` (1), effectivity clause.**  The printed two-sided bridge,
not the one-sided auxiliary bridge, has a recursive presentation on `x,y,t`.
-/
theorem bridge_recursivePresentation {C : Type} [Group C]
    (p : Higman.RecursivePresentation C) :
    Nonempty (Higman.FGRecursive (BGroup (seq p.gen))) := by
  have hspan : Subgroup.closure (Set.range (seq p.gen)) = ⊤ :=
    closure_range_seq p.gen p.spans
  exact ⟨{
    rank := 2
    π := qC (seq p.gen)
    π_surjective := qC_surjective _ hspan
    re := Effectivity.rePred_qC_of_spans p.gen p.spans p.re
  }⟩

/-- **`lem:bridge` (1), exactly as printed.** -/
theorem manuscriptBridge_one {C : Type} [Group C]
    (p : Higman.RecursivePresentation C) :
    Function.Injective (embC (seq p.gen)) ∧
      Subgroup.closure (bridgeGens (seq p.gen)) = ⊤ ∧
      Function.Surjective (qC (seq p.gen)) ∧
      Nonempty (Higman.FGRecursive (BGroup (seq p.gen))) := by
  have hspan : Subgroup.closure (Set.range (seq p.gen)) = ⊤ :=
    closure_range_seq p.gen p.spans
  exact ⟨embC_injective _, closure_gens_eq_top_of_spans _ hspan,
    qC_surjective _ hspan, bridge_recursivePresentation p⟩

end Bridge
end MFRecognition
end Manuscript
end GroupApproximation
