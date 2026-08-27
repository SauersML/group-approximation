import GroupApproximation.Higman.OmegaFatShearedFirstCoordinateMatched
import GroupApproximation.Algebra.HNNFinitePresentation

/-!
# The first matched sheared edge in a finite semantic overgroup

Fix a final width `m ≥ 1` and put two copies of its finite semantic base side
by side.  The source cyclic link is placed in the left copy and its
coefficient-one target in the right copy.  Their common width-zero free basis
gives an explicit associated-subgroup equivalence.  The resulting HNN
extension is finitely presented and torsion-free, contains two injective
copies of the whole semantic base, and those copies agree on the matched
abstract singleton after conjugating the target copy by the stable letter.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open HNNExtension

/-- The source singleton edge in the left semantic copy. -/
noncomputable def fatShearedFirstPairSource
    (m : ℕ) (hm : 1 ≤ m) :
    FreeGroup ↥(blockSet 0) →*
      (FatCent3 m × F₃) × (FatCent3 m × F₃) :=
  (fatShearedCoordinateSource m 0 (Nat.zero_le m)).prod 1

/-- The coefficient-one target edge in the right semantic copy. -/
noncomputable def fatShearedFirstPairTarget
    (m : ℕ) (hm : 1 ≤ m) :
    FreeGroup ↥(blockSet 0) →*
      (FatCent3 m × F₃) × (FatCent3 m × F₃) :=
  (1 : FreeGroup ↥(blockSet 0) →* FatCent3 m × F₃).prod
    (fatShearedCoordinateTarget m 0 hm)

theorem fatShearedFirstPairSource_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fatShearedFirstPairSource m hm) := by
  intro u v huv
  apply fatShearedCoordinateSource_injective m 0 (Nat.zero_le m)
  exact congrArg Prod.fst huv

theorem fatShearedFirstPairTarget_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fatShearedFirstPairTarget m hm) := by
  intro u v huv
  apply fatShearedCoordinateTarget_injective m 0 hm
  exact congrArg Prod.snd huv

/-- The explicit finite-rank edge between the two semantic copies. -/
noncomputable def fatShearedFirstPairEdge
    (m : ℕ) (hm : 1 ≤ m) :
    ExplicitFreeEdge.Data ↥(blockSet 0)
      ((FatCent3 m × F₃) × (FatCent3 m × F₃)) where
  source := fatShearedFirstPairSource m hm
  target := fatShearedFirstPairTarget m hm
  source_injective := fatShearedFirstPairSource_injective m hm
  target_injective := fatShearedFirstPairTarget_injective m hm

/-- The source associated subgroup pulls back through the left semantic copy
to exactly the fixed-width width-zero sheared range. -/
theorem fatShearedFirstPair_source_comap
    (m : ℕ) (hm : 1 ≤ m) :
    (ExplicitFreeEdge.sourceSubgroup (fatShearedFirstPairEdge m hm)).comap
        (MonoidHom.inl (FatCent3 m × F₃) (FatCent3 m × F₃)) =
      fatShearedCoordinateRange m 0 (Nat.zero_le m) := by
  ext x
  constructor
  · rintro ⟨w, -, hw⟩
    refine ⟨w, ?_⟩
    exact congrArg Prod.fst hw
  · rintro ⟨w, rfl⟩
    refine ⟨w, Subgroup.mem_top w, ?_⟩
    rfl

/-- The target associated subgroup pulls back through the right semantic copy
to exactly the coefficient-one sheared range. -/
theorem fatShearedFirstPair_target_comap
    (m : ℕ) (hm : 1 ≤ m) :
    (ExplicitFreeEdge.targetSubgroup (fatShearedFirstPairEdge m hm)).comap
        (MonoidHom.inr (FatCent3 m × F₃) (FatCent3 m × F₃)) =
      (fatShearedCoordinateTarget m 0 hm).range := by
  ext x
  constructor
  · rintro ⟨w, -, hw⟩
    refine ⟨w, ?_⟩
    exact congrArg Prod.snd hw
  · rintro ⟨w, rfl⟩
    refine ⟨w, Subgroup.mem_top w, ?_⟩
    rfl

/-- The finite semantic HNN overgroup realizing the first adjacent
coefficient match. -/
noncomputable abbrev FatShearedFirstSemanticExtension
    (m : ℕ) (hm : 1 ≤ m) : Type :=
  ExplicitFreeEdge.Extension (fatShearedFirstPairEdge m hm)

/-- The whole semantic base embedded through the left factor. -/
noncomputable def fatShearedFirstSemanticSourceEmb
    (m : ℕ) (hm : 1 ≤ m) :
    FatCent3 m × F₃ →* FatShearedFirstSemanticExtension m hm :=
  (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
    FatShearedFirstSemanticExtension m hm).comp
      (MonoidHom.inl (FatCent3 m × F₃) (FatCent3 m × F₃))

/-- The right semantic copy, pulled back across the stable letter. -/
noncomputable def fatShearedFirstSemanticTargetEmb
    (m : ℕ) (hm : 1 ≤ m) :
    FatCent3 m × F₃ →* FatShearedFirstSemanticExtension m hm :=
  (MulAut.conj
      (t : FatShearedFirstSemanticExtension m hm)⁻¹).toMonoidHom.comp
    ((of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
      FatShearedFirstSemanticExtension m hm).comp
        (MonoidHom.inr (FatCent3 m × F₃) (FatCent3 m × F₃)))

theorem fatShearedFirstSemanticSourceEmb_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fatShearedFirstSemanticSourceEmb m hm) :=
  (HNNExtension.of_injective
      (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))).comp
    MonoidHom.inl_injective

theorem fatShearedFirstSemanticTargetEmb_injective
    (m : ℕ) (hm : 1 ≤ m) :
    Function.Injective (fatShearedFirstSemanticTargetEmb m hm) :=
  (MulAut.conj
      (t : FatShearedFirstSemanticExtension m hm)⁻¹).injective.comp
    ((HNNExtension.of_injective
      (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))).comp
        MonoidHom.inr_injective)

/-- **Matched semantic identity.**  On the common abstract singleton word,
the left source embedding and the conjugated right target embedding agree
literally in the shared finite HNN overgroup. -/
theorem fatShearedFirstSemantic_restrict_eq
    (m : ℕ) (hm : 1 ≤ m) :
    (fatShearedFirstSemanticTargetEmb m hm).comp
        (fatShearedCoordinateTarget m 0 hm) =
      (fatShearedFirstSemanticSourceEmb m hm).comp
        (fatShearedCoordinateSource m 0 (Nat.zero_le m)) := by
  refine FreeGroup.ext_hom _ _ fun beta ↦ ?_
  have h := ExplicitFreeEdge.stable_conj_source
    (fatShearedFirstPairEdge m hm) (FreeGroup.of beta)
  change (t : FatShearedFirstSemanticExtension m hm) *
      of (fatShearedFirstPairSource m hm (FreeGroup.of beta)) * t⁻¹ =
    of (fatShearedFirstPairTarget m hm (FreeGroup.of beta)) at h
  change t⁻¹ *
      of (1, fatShearedCoordinateTarget m 0 hm (FreeGroup.of beta)) * t =
    of (fatShearedCoordinateSource m 0 (Nat.zero_le m)
      (FreeGroup.of beta), 1)
  rw [← h]
  group

/-- The matched semantic overgroup is finitely presented. -/
theorem fatShearedFirstSemanticExtension_finitelyPresented
    (m : ℕ) (hm : 1 ≤ m) :
    Group.IsFinitelyPresented (FatShearedFirstSemanticExtension m hm) := by
  letI : Group.IsFinitelyPresented (FatCent3 m) :=
    isFinitelyPresented_fatCent3 m
  letI : Group.IsFinitelyPresented (FatCent3 m × F₃) := inferInstance
  letI : Group.IsFinitelyPresented
      ((FatCent3 m × F₃) × (FatCent3 m × F₃)) := inferInstance
  letI : Subsingleton ↥(blockSet 0) := blockSet_zero_subsingleton
  letI : Finite ↥(blockSet 0) := Finite.of_injective
    (fun _ : ↥(blockSet 0) => ()) (fun _ _ _ => Subsingleton.elim _ _)
  letI : Group.FG (FreeGroup ↥(blockSet 0)) := inferInstance
  letI : Group.FG
      ↥(ExplicitFreeEdge.sourceSubgroup (fatShearedFirstPairEdge m hm)) :=
    Group.fg_of_surjective
      (ExplicitFreeEdge.sourceEquiv (fatShearedFirstPairEdge m hm)).toMonoidHom
      (ExplicitFreeEdge.sourceEquiv (fatShearedFirstPairEdge m hm)).surjective
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension
    (ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))

/-- The matched semantic overgroup is torsion-free. -/
theorem fatShearedFirstSemanticExtension_torsionFree
    (m : ℕ) (hm : 1 ≤ m) :
    IsPowerTorsionFree (FatShearedFirstSemanticExtension m hm) :=
  HNNBritton.isPowerTorsionFree_hnn
    (ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))
    (IsPowerTorsionFree.prod
      (IsPowerTorsionFree.prod (isPowerTorsionFree_fatCent3 m)
        IsPowerTorsionFree.of_isMulTorsionFree)
      (IsPowerTorsionFree.prod (isPowerTorsionFree_fatCent3 m)
        IsPowerTorsionFree.of_isMulTorsionFree))

/-! ## The shared semantic cutter and its two exact comaps -/

/-- The source associated subgroup, embedded in the finite HNN overgroup. -/
noncomputable def fatShearedFirstSemanticCutter
    (m : ℕ) (hm : 1 ≤ m) :
    Subgroup (FatShearedFirstSemanticExtension m hm) :=
  (ExplicitFreeEdge.sourceSubgroup (fatShearedFirstPairEdge m hm)).map
    (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
      FatShearedFirstSemanticExtension m hm)

theorem fatShearedFirstPairSource_fg
    (m : ℕ) (hm : 1 ≤ m) :
    (ExplicitFreeEdge.sourceSubgroup
      (fatShearedFirstPairEdge m hm)).FG := by
  letI : Subsingleton ↥(blockSet 0) := blockSet_zero_subsingleton
  letI : Finite ↥(blockSet 0) := Finite.of_injective
    (fun _ : ↥(blockSet 0) => ()) (fun _ _ _ => Subsingleton.elim _ _)
  letI : Group.FG (FreeGroup ↥(blockSet 0)) := inferInstance
  exact Group.fg_of_surjective
    (ExplicitFreeEdge.sourceEquiv
      (fatShearedFirstPairEdge m hm)).toMonoidHom
    (ExplicitFreeEdge.sourceEquiv
      (fatShearedFirstPairEdge m hm)).surjective

theorem fatShearedFirstSemanticCutter_fg
    (m : ℕ) (hm : 1 ≤ m) :
    (fatShearedFirstSemanticCutter m hm).FG :=
  fg_map (fatShearedFirstPairSource_fg m hm)
    (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
      FatShearedFirstSemanticExtension m hm)

/-- The source-associated cutter is also the conjugated target-associated
cutter.  This is the subgroup-level form of the HNN relation. -/
theorem fatShearedFirstSemanticCutter_eq_target
    (m : ℕ) (hm : 1 ≤ m) :
    fatShearedFirstSemanticCutter m hm =
      ((ExplicitFreeEdge.targetSubgroup
          (fatShearedFirstPairEdge m hm)).map
        (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
          FatShearedFirstSemanticExtension m hm)).map
        (MulAut.conj
          (t : FatShearedFirstSemanticExtension m hm)⁻¹).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    let aa : ExplicitFreeEdge.sourceSubgroup
        (fatShearedFirstPairEdge m hm) := ⟨a, ha⟩
    let b := ExplicitFreeEdge.edgeEquiv
      (fatShearedFirstPairEdge m hm) aa
    refine ⟨of (b : (FatCent3 m × F₃) × (FatCent3 m × F₃)),
      ⟨(b : (FatCent3 m × F₃) × (FatCent3 m × F₃)), b.property, rfl⟩, ?_⟩
    have h := HNNExtension.equiv_eq_conj
      (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm)) aa
    change t⁻¹ * of (b : (FatCent3 m × F₃) × (FatCent3 m × F₃)) * t =
      of a
    rw [h]
    group
  · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    let bb : ExplicitFreeEdge.targetSubgroup
        (fatShearedFirstPairEdge m hm) := ⟨b, hb⟩
    let a := (ExplicitFreeEdge.edgeEquiv
      (fatShearedFirstPairEdge m hm)).symm bb
    refine ⟨(a : (FatCent3 m × F₃) × (FatCent3 m × F₃)), a.property, ?_⟩
    have h := HNNExtension.equiv_eq_conj
      (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm)) a
    have hab : ((ExplicitFreeEdge.edgeEquiv
        (fatShearedFirstPairEdge m hm) a :
          ExplicitFreeEdge.targetSubgroup
            (fatShearedFirstPairEdge m hm)) :
          (FatCent3 m × F₃) × (FatCent3 m × F₃)) = b := by
      change (((ExplicitFreeEdge.edgeEquiv
        (fatShearedFirstPairEdge m hm)).apply
          ((ExplicitFreeEdge.edgeEquiv
            (fatShearedFirstPairEdge m hm)).symm bb) :
              ExplicitFreeEdge.targetSubgroup
                (fatShearedFirstPairEdge m hm)) :
            (FatCent3 m × F₃) × (FatCent3 m × F₃)) = b
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hab] at h
    change of (a : (FatCent3 m × F₃) × (FatCent3 m × F₃)) =
      t⁻¹ * of b * t
    rw [h]
    group

/-- Exact source-side cutter comap in the finite semantic overgroup. -/
theorem fatShearedFirstSemanticCutter_comap_source
    (m : ℕ) (hm : 1 ≤ m) :
    (fatShearedFirstSemanticCutter m hm).comap
        (fatShearedFirstSemanticSourceEmb m hm) =
      fatShearedCoordinateRange m 0 (Nat.zero_le m) := by
  change (((ExplicitFreeEdge.sourceSubgroup
      (fatShearedFirstPairEdge m hm)).map
        (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
          FatShearedFirstSemanticExtension m hm)).comap
      (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
        FatShearedFirstSemanticExtension m hm)).comap
      (MonoidHom.inl (FatCent3 m × F₃) (FatCent3 m × F₃)) = _
  rw [Subgroup.comap_map_eq_self_of_injective
    (HNNExtension.of_injective
      (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))),
    fatShearedFirstPair_source_comap]

/-- Exact target-side cutter comap under the conjugated whole-base embedding. -/
theorem fatShearedFirstSemanticCutter_comap_target
    (m : ℕ) (hm : 1 ≤ m) :
    (fatShearedFirstSemanticCutter m hm).comap
        (fatShearedFirstSemanticTargetEmb m hm) =
      (fatShearedCoordinateTarget m 0 hm).range := by
  rw [fatShearedFirstSemanticCutter_eq_target]
  change (((((ExplicitFreeEdge.targetSubgroup
      (fatShearedFirstPairEdge m hm)).map
        (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
          FatShearedFirstSemanticExtension m hm)).map
      (MulAut.conj
        (t : FatShearedFirstSemanticExtension m hm)⁻¹).toMonoidHom).comap
      (MulAut.conj
        (t : FatShearedFirstSemanticExtension m hm)⁻¹).toMonoidHom).comap
      (of : ((FatCent3 m × F₃) × (FatCent3 m × F₃)) →*
        FatShearedFirstSemanticExtension m hm)).comap
      (MonoidHom.inr (FatCent3 m × F₃) (FatCent3 m × F₃)) = _
  rw [Subgroup.comap_map_eq_self_of_injective
      (MulAut.conj
        (t : FatShearedFirstSemanticExtension m hm)⁻¹).injective,
    Subgroup.comap_map_eq_self_of_injective
      (HNNExtension.of_injective
        (φ := ExplicitFreeEdge.edgeEquiv (fatShearedFirstPairEdge m hm))),
    fatShearedFirstPair_target_comap]

/-- The source range packaged with the actual shared semantic cutter. -/
noncomputable def fatShearedFirstSemanticSourceWitness
    (m : ℕ) (hm : 1 ≤ m) :
    TorsionFreeBenignWitness
      (fatShearedCoordinateRange m 0 (Nat.zero_le m)) := by
  letI : Group.IsFinitelyPresented
      (FatShearedFirstSemanticExtension m hm) :=
    fatShearedFirstSemanticExtension_finitelyPresented m hm
  exact
    { witness :=
        { K := FatShearedFirstSemanticExtension m hm
          emb := fatShearedFirstSemanticSourceEmb m hm
          emb_injective := fatShearedFirstSemanticSourceEmb_injective m hm
          L := fatShearedFirstSemanticCutter m hm
          L_fg := fatShearedFirstSemanticCutter_fg m hm
          comap_eq := fatShearedFirstSemanticCutter_comap_source m hm }
      torsionFree := fatShearedFirstSemanticExtension_torsionFree m hm }

/-- The adjacent coefficient-one range is cut by the same finite semantic
cutter under the matched target embedding. -/
noncomputable def fatShearedFirstSemanticTargetWitness
    (m : ℕ) (hm : 1 ≤ m) :
    TorsionFreeBenignWitness
      ((fatShearedCoordinateTarget m 0 hm).range) := by
  letI : Group.IsFinitelyPresented
      (FatShearedFirstSemanticExtension m hm) :=
    fatShearedFirstSemanticExtension_finitelyPresented m hm
  exact
    { witness :=
        { K := FatShearedFirstSemanticExtension m hm
          emb := fatShearedFirstSemanticTargetEmb m hm
          emb_injective := fatShearedFirstSemanticTargetEmb_injective m hm
          L := fatShearedFirstSemanticCutter m hm
          L_fg := fatShearedFirstSemanticCutter_fg m hm
          comap_eq := fatShearedFirstSemanticCutter_comap_target m hm }
      torsionFree := fatShearedFirstSemanticExtension_torsionFree m hm }

theorem benignTF_fatShearedFirstSemanticSource
    (m : ℕ) (hm : 1 ≤ m) :
    BenignTF (fatShearedCoordinateRange m 0 (Nat.zero_le m)) :=
  ⟨fatShearedFirstSemanticSourceWitness m hm⟩

theorem benignTF_fatShearedFirstSemanticTarget
    (m : ℕ) (hm : 1 ≤ m) :
    BenignTF ((fatShearedCoordinateTarget m 0 hm).range) :=
  ⟨fatShearedFirstSemanticTargetWitness m hm⟩

end Omega
end Higman
end GroupApproximation
