import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudget
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCore
import GroupApproximation.Dynamics.ReturnRingCrossedProduct
import GroupApproximation.Algebra.CornerLEF
import GroupApproximation.Algebra.LEFRingDirectedUnion
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the core meets the section inside the induced core

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1745:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.

This module proves the inclusion `C ∩ Y ⊆ CR(S_C)` along the printed route.  The inclusion
`CR(S_C) ⊆ C ∩ Y` is ct-rank-budget's `coe_mem_chainRecurrentSet_of_firstReturn`
(`DynamicRankBudgetInducedCore`).

* `isReturnSection_restrict`: a return section `C` of `T` restricts to a return section `C ∩ Y` of
  `T|_Y` for every invariant `Y`, with the same return times (`returnTime_restrict`) and the
  first-return map of `C ∩ Y` equal to that of `C` on its points (`firstReturnHomeomorph_restrict_coe`).
* `mem_chainRecurrentSet_firstReturn_of_pieces`, over `CoreModelsLEFStatement` and
  `CoreRingReflectionStatement`.  The return ring of `C ∩ Y` for `T|_Y` is the corner `p_{C∩Y} R_Y p_{C∩Y}`
  (`returnRingHom`, `returnRingHom_injective`).  `R_Y` is LEF, hence so is the corner
  (`Pestov91.IsLEFRing.corner`) and the return ring (`Pestov91.IsLEFRing.of_injective`).  Theorem
  `thm:core-ring-reflection` for `(C ∩ Y, S_{C∩Y})` makes every point chain recurrent, and the inclusion
  `C ∩ Y → C` carries `S_{C∩Y}`-chains to `S_C`-chains (`Dynamics.mapsTo_chainRecurrentSet`).
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ClopenCrossedProduct

section Restrict

variable {X : Type*} [TopologicalSpace X] {T : X ≃ₜ X} {Y : Set X} {r : ℕ} {C : Set X}

theorem coe_restrictHomeo_zpow_apply (hY : T '' Y = Y) (n : ℤ) (y : Y) :
    (((restrictHomeo T hY) ^ n) y : X) = (T ^ n) y :=
  semiconj_zpow (π := Subtype.val) (fun _ => rfl) n y

/-- **Restricting a return section to an invariant set.** -/
theorem isReturnSection_restrict (hC : IsReturnSection T r C) (hY : T '' Y = Y) :
    IsReturnSection (restrictHomeo T hY) r (Subtype.val ⁻¹' C : Set Y) where
  isClopen := hC.isClopen.preimage continuous_subtype_val
  disjoint_image j hj₁ hj₂ := by
    refine Set.disjoint_left.2 fun y hy hyimg => ?_
    obtain ⟨z, hz, rfl⟩ := hyimg
    exact Set.disjoint_left.1 (hC.disjoint_image j hj₁ hj₂) hy
      ⟨(z : X), hz, (coe_restrictHomeo_zpow_apply hY (j : ℤ) z).symm⟩
  exists_mem_image y := by
    obtain ⟨j, hj, c, hc, hcy⟩ := hC.exists_mem_image (y : X)
    refine ⟨j, hj, ((restrictHomeo T hY) ^ (-j)) y, ?_, ?_⟩
    · show (((restrictHomeo T hY) ^ (-j)) y : X) ∈ C
      rw [coe_restrictHomeo_zpow_apply, ← hcy, ← Homeomorph.mul_apply, ← zpow_add, neg_add_cancel,
        zpow_zero, Homeomorph.one_apply]
      exact hc
    · rw [← Homeomorph.mul_apply, ← zpow_add, add_neg_cancel, zpow_zero, Homeomorph.one_apply]

/-- The return times of the restricted section are those of `C`. -/
theorem returnTime_restrict (hC : IsReturnSection T r C) (hY : T '' Y = Y) (y : Y) :
    returnTime (restrictHomeo T hY) (Subtype.val ⁻¹' C : Set Y) y = returnTime T C y := by
  obtain ⟨h₁, h₂⟩ := returnTime_spec hC (y : X)
  refine returnTime_eq_of (isReturnSection_restrict hC hY) y h₁ ?_ fun j hj₁ hj₂ hjC => ?_
  · show (((restrictHomeo T hY) ^ (returnTime T C (y : X) : ℤ)) y : X) ∈ C
    rw [coe_restrictHomeo_zpow_apply]
    exact h₂
  · refine returnTime_min hC (y : X) hj₁ hj₂ ?_
    have hjC' : (((restrictHomeo T hY) ^ (j : ℤ)) y : X) ∈ C := hjC
    rwa [coe_restrictHomeo_zpow_apply] at hjC'

/-- The first-return map of `C ∩ Y` is that of `C` on its points. -/
theorem firstReturnHomeomorph_restrict_coe (hC : IsReturnSection T r C) (hY : T '' Y = Y)
    (z : (Subtype.val ⁻¹' C : Set Y)) :
    ((firstReturnHomeomorph (isReturnSection_restrict hC hY) z : Y) : X) =
      (firstReturnHomeomorph hC ⟨((z : Y) : X), z.2⟩ : X) := by
  rw [firstReturnHomeomorph_apply, firstReturnHomeomorph_apply, coe_restrictHomeo_zpow_apply,
    returnTime_restrict hC hY]

end Restrict

/-- **`C ∩ Y ⊆ CR(S_C)`** (tex 1743–1745), along the printed route, over Lemma `lem:chain-core-models`
("$R_Y$ is LEF") and Theorem `thm:core-ring-reflection`. -/
theorem mem_chainRecurrentSet_firstReturn_of_pieces (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) {x : X} (hxC : x ∈ C)
    (hxY : x ∈ Dynamics.chainRecurrentSet T) :
    (⟨x, hxC⟩ : C) ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : T '' Dynamics.chainRecurrentSet T = Dynamics.chainRecurrentSet T := image_core T
  have hC' := isReturnSection_restrict hC hY
  haveI : CompactSpace (Dynamics.chainRecurrentSet T) :=
    isCompact_iff_compactSpace.mp (Dynamics.isClosed_chainRecurrentSet T.continuous).isCompact
  haveI : CompactSpace (Subtype.val ⁻¹' C : Set (Dynamics.chainRecurrentSet T)) :=
    isCompact_iff_compactSpace.mp hC'.isClopen.isClosed.isCompact
  haveI : Nonempty (Subtype.val ⁻¹' C : Set (Dynamics.chainRecurrentSet T)) :=
    ⟨⟨⟨x, hxY⟩, hxC⟩⟩
  have hLEF_Y := hModels X T (ZMod 2)
  have hLEF_corner :=
    hLEF_Y.corner (returnP (ZMod 2) hC') (isIdempotentElem_returnP (ZMod 2) hC')
  have hLEF_S := Pestov91.IsLEFRing.of_injective hLEF_corner (returnRingHom (ZMod 2) hC')
    (returnRingHom_injective (ZMod 2) hC')
  have hall := (hRefl _ (firstReturnHomeomorph hC') (ZMod 2)).2.2.1 hLEF_S
  have hcont : Continuous (fun z : (Subtype.val ⁻¹' C : Set (Dynamics.chainRecurrentSet T)) =>
      (⟨((z : Dynamics.chainRecurrentSet T) : X), z.2⟩ : C)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hsemi : Function.Semiconj
      (fun z : (Subtype.val ⁻¹' C : Set (Dynamics.chainRecurrentSet T)) =>
        (⟨((z : Dynamics.chainRecurrentSet T) : X), z.2⟩ : C))
      (firstReturnHomeomorph hC') (firstReturnHomeomorph hC) :=
    fun z => Subtype.ext (firstReturnHomeomorph_restrict_coe hC hY z)
  exact Dynamics.mapsTo_chainRecurrentSet hcont hsemi (hall ⟨⟨x, hxY⟩, hxC⟩)

/-- **The induced core is `C ∩ Y`** (tex 1743): `CR(S_C) = C ∩ CR(T)`, over the same two pieces.
The inclusion `CR(S_C) ⊆ C ∩ Y` is `coe_mem_chainRecurrentSet_of_firstReturn`. -/
theorem image_chainRecurrentSet_firstReturn_of_pieces (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) :
    Subtype.val '' Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) =
      C ∩ Dynamics.chainRecurrentSet T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, coe_mem_chainRecurrentSet_of_firstReturn hC hy⟩
  · rintro ⟨hxC, hxY⟩
    exact ⟨⟨x, hxC⟩, mem_chainRecurrentSet_firstReturn_of_pieces hRefl hModels T hC hxC hxY, rfl⟩

end GroupApproximation.ChainCore.DynamicRankBudget

open GroupApproximation.ChainCore.DynamicRankBudget

#audit_axioms isReturnSection_restrict
#audit_axioms returnTime_restrict
#audit_axioms mem_chainRecurrentSet_firstReturn_of_pieces
#audit_axioms image_chainRecurrentSet_firstReturn_of_pieces
