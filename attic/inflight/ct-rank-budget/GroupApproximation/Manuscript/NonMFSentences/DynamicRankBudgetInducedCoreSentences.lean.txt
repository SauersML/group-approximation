import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCoreClosed
import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetReturnTransientIdeal
import GroupApproximation.Dynamics.ReturnRingCrossedProduct
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the four sentences after "The induced core is `C ∩ Y`"

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1750:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.  Theorem~\ref{thm:core-ring-reflection}
> applied to this subsystem makes every one of its points chain recurrent
> in $X$, proving the reverse inclusion.  The return transient ideal
> is therefore $J=p_CIp_C$.

The first sentence is `printedInducedCore_closed` (`DynamicRankBudgetInducedCoreClosed`).  This module
states each of the other four as a named Prop at the printed generality (every return section, every
finite field) and closes it along the printed route, over the closed inputs
`coreRingReflectionStatement_holds` (`ChainCoreClosures`) and `coreModelsLEFStatement` (ms-core-2):

* `printedInducedCoreCorner_closed`: the return ring of `C ∩ Y` for `T|_Y` is isomorphic to the corner
  `p R_Y p` of the LEF ring `R_Y`, hence LEF, and `C ∩ Y ⊆ CR(S_C)` (ms-core-1's
  `mem_chainRecurrentSet_firstReturn_of_pieces`);
* `printedCoreSaturationLEF_closed`: the saturation `Y'` of `CR(S_C)` through the towers is closed and
  invariant, and `R_{Y'}` is a corner of a matrix ring over an LEF ring, hence LEF;
* `printedCoreSaturationRecurrent_closed`: Theorem `thm:core-ring-reflection` for `(Y', T|_{Y'})` puts
  `Y'` inside `CR(T)`, so `CR(S_C) ⊆ C ∩ CR(T)`;
* `printedReturnTransientIdeal_closed`: under `returnRingEquiv : R_{S_C} ≅ P_C`, an element lies in the
  return transient ideal exactly when its image lies in `p_C I p_C`.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ClopenCrossedProduct
open Multiplicative (ofAdd toAdd)

/-! ## tex 1743–1745: the return ring of `C ∩ Y` is a corner of `R_Y` -/

/-- **tex 1743–1745**, "Indeed its return ring is a corner of the LEF ring $R_Y$, so it lies in the
induced chain-recurrent core": for a return section `C`, the return ring of `C ∩ Y` for `T|_Y`
(`Y = CR(T)`) is isomorphic to the corner `P_{C∩Y}` of `R_Y`, `R_Y` and the return ring are LEF, and
`C ∩ Y` lies in the chain-recurrent set of `S_C`. -/
def PrintedInducedCoreCorner : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : IsReturnSection T r C),
    (∀ (k : Type) [Field k] [Finite k],
      Nonempty (ClopenCrossedProduct (firstReturnHomeomorph (isReturnSection_restrict hC (image_core T))) k ≃+*
          ReturnCorner k (isReturnSection_restrict hC (image_core T))) ∧
        Pestov91.IsLEFRing (ClopenCrossedProduct (restrictHomeo T (image_core T)) k) ∧
        Pestov91.IsLEFRing
          (ClopenCrossedProduct (firstReturnHomeomorph (isReturnSection_restrict hC (image_core T))) k)) ∧
      C ∩ Dynamics.chainRecurrentSet T ⊆
        Subtype.val '' Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)

theorem printedInducedCoreCorner_closed : PrintedInducedCoreCorner := by
  intro X _ _ _ _ T r C hC
  refine ⟨fun k _ _ => ?_, fun x hx => ⟨⟨x, hx.1⟩,
    mem_chainRecurrentSet_firstReturn_of_pieces
      GroupApproximation.ChainCore.ChainCoreClosures.coreRingReflectionStatement_holds
      GroupApproximation.ChainCore.coreModelsLEFStatement T hC hx.1 hx.2, rfl⟩⟩
  have hY := GroupApproximation.ChainCore.coreModelsLEFStatement X T k
  refine ⟨⟨returnRingEquiv k (isReturnSection_restrict hC (image_core T))⟩, hY, ?_⟩
  exact Pestov91.IsLEFRing.of_injective
    (hY.corner (returnP k (isReturnSection_restrict hC (image_core T)))
      (isIdempotentElem_returnP k (isReturnSection_restrict hC (image_core T))))
    (returnRingHom k (isReturnSection_restrict hC (image_core T)))
    (returnRingHom_injective k (isReturnSection_restrict hC (image_core T)))

/-! ## tex 1745–1747: the saturation is LEF -/

/-- The saturation `Y'` of `CR(S_C)` through the towers has ring `R_{Y'}` isomorphic to a corner of a
matrix ring over an LEF ring. -/
theorem exists_corner_matrix_returnSaturation {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) (k : Type) [Field k] [Finite k] :
    ∃ (N : ℕ) (A : Type) (_ : Ring A) (e : Matrix (Fin N) (Fin N) A) (he : IsIdempotentElem e),
      Pestov91.IsLEFRing A ∧
        Nonempty (ClopenCrossedProduct (restrictHomeo T (image_returnSaturation
            (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)))) k ≃+*
          Corner (Matrix (Fin N) (Fin N) A) e he) := by
  have hr : 1 ≤ r := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨j, hj, -⟩ := hC.exists_mem_image x
    have := abs_nonneg j
    omega
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact
  haveI : Nonempty C := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨j, -, c, hc, -⟩ := hC.exists_mem_image x
    exact ⟨⟨c, hc⟩⟩
  have hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) ↔
      z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) :=
    fun z => Dynamics.apply_mem_chainRecurrentSet_iff (firstReturnHomeomorph hC)
  have hY : T '' returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) =
      returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    image_returnSaturation _
  have hC' := isReturnSection_restrict hC hY
  let π : C((Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) : Set C),
      (Subtype.val ⁻¹' C :
        Set (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))))) :=
    ⟨fun z => ⟨⟨((z : C) : X), subset_returnSaturation (z : C) z.2⟩, (z : C).2⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  have hπ : ∀ z, π (restrictHomeo (firstReturnHomeomorph hC) (image_core (firstReturnHomeomorph hC)) z) =
      firstReturnHomeomorph hC' (π z) := fun z =>
    Subtype.ext (Subtype.ext (firstReturnHomeomorph_restrict_coe hC hY (π z)).symm)
  have hsurj : Function.Surjective π := by
    rintro ⟨⟨w, hwY⟩, hwC⟩
    exact ⟨⟨⟨w, hwC⟩, (mem_returnSaturation_iff hC hZ ⟨w, hwC⟩).1 hwY⟩, rfl⟩
  have hLEF_S : Pestov91.IsLEFRing (ClopenCrossedProduct (firstReturnHomeomorph hC') k) :=
    Pestov91.IsLEFRing.of_injective
      (GroupApproximation.ChainCore.coreModelsLEFStatement C (firstReturnHomeomorph hC) k)
      (comap k π hπ) (comap_injective k π hπ hsurj)
  have hLEF_P : Pestov91.IsLEFRing (ReturnCorner k hC') :=
    Pestov91.IsLEFRing.of_injective hLEF_S (returnRingEquiv k hC').symm.toRingHom
      (returnRingEquiv k hC').symm.injective
  have hLEF_base : Pestov91.IsLEFRing (returnTowerUnits k hC' hr).Base := hLEF_P
  exact ⟨2 * r - 1, (returnTowerUnits k hC' hr).Base, inferInstance,
    (returnTowerUnits k hC' hr).toMatrix 1, (returnTowerUnits k hC' hr).isIdempotentElem_toMatrix_one,
    hLEF_base, ⟨(returnTowerUnits k hC' hr).cornerEquiv⟩⟩

/-- **tex 1745–1747**, "Conversely, saturating that core through the finite towers gives a closed
invariant subsystem whose ring is a corner of a matrix ring over an LEF ring, hence LEF": the
saturation `Y'` of `CR(S_C)` is closed and invariant, and over every finite field `R_{Y'}` is a corner
of a matrix ring over an LEF ring, and is LEF. -/
def PrintedCoreSaturationLEF : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : IsReturnSection T r C),
    IsClosed (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))) ∧
      T '' returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) =
        returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) ∧
      ∀ (k : Type) [Field k] [Finite k],
        (∃ (N : ℕ) (A : Type) (_ : Ring A) (e : Matrix (Fin N) (Fin N) A) (he : IsIdempotentElem e),
          Pestov91.IsLEFRing A ∧
            Nonempty (ClopenCrossedProduct (restrictHomeo T (image_returnSaturation
                (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)))) k ≃+*
              Corner (Matrix (Fin N) (Fin N) A) e he)) ∧
          Pestov91.IsLEFRing (ClopenCrossedProduct (restrictHomeo T (image_returnSaturation
            (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)))) k)

theorem printedCoreSaturationLEF_closed : PrintedCoreSaturationLEF := by
  intro X _ _ _ _ T r C hC
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact
  have hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) ↔
      z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) :=
    fun z => Dynamics.apply_mem_chainRecurrentSet_iff (firstReturnHomeomorph hC)
  have hZc : IsClosed (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    Dynamics.isClosed_chainRecurrentSet (firstReturnHomeomorph hC).continuous
  refine ⟨isClosed_returnSaturation hC hZ hZc, image_returnSaturation _, fun k _ _ => ?_⟩
  obtain ⟨N, A, _, e, he, hA, ⟨φ⟩⟩ := exists_corner_matrix_returnSaturation T hC k
  exact ⟨⟨N, A, inferInstance, e, he, hA, ⟨φ⟩⟩,
    Pestov91.IsLEFRing.of_injective ((hA.matrix (Fin N)).corner e he) φ.toRingHom φ.injective⟩

/-! ## tex 1747–1749: core-ring reflection for the saturation -/

/-- **tex 1747–1749**, "Theorem~\ref{thm:core-ring-reflection} applied to this subsystem makes every
one of its points chain recurrent in $X$, proving the reverse inclusion": the saturation of `CR(S_C)`
lies in `CR(T)`, so `CR(S_C) ⊆ C ∩ CR(T)`. -/
def PrintedCoreSaturationRecurrent : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : IsReturnSection T r C),
    returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) ⊆
        Dynamics.chainRecurrentSet T ∧
      Subtype.val '' Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) ⊆
        C ∩ Dynamics.chainRecurrentSet T

theorem printedCoreSaturationRecurrent_closed : PrintedCoreSaturationRecurrent := by
  intro X _ _ _ _ T r C hC
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact
  have hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) ↔
      z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) :=
    fun z => Dynamics.apply_mem_chainRecurrentSet_iff (firstReturnHomeomorph hC)
  have hZc : IsClosed (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    Dynamics.isClosed_chainRecurrentSet (firstReturnHomeomorph hC).continuous
  have hY : T '' returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) =
      returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    image_returnSaturation _
  haveI : CompactSpace
      (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))) :=
    isCompact_iff_compactSpace.mp (isClosed_returnSaturation hC hZ hZc).isCompact
  have hsub : returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) ⊆
      Dynamics.chainRecurrentSet T := by
    intro x hx
    haveI : Nonempty
        (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))) :=
      ⟨⟨x, hx⟩⟩
    obtain ⟨N, A, _, e, he, hA, ⟨φ⟩⟩ := exists_corner_matrix_returnSaturation T hC (ZMod 2)
    have hLEF_Y : Pestov91.IsLEFRing (ClopenCrossedProduct (restrictHomeo T hY) (ZMod 2)) :=
      Pestov91.IsLEFRing.of_injective ((hA.matrix (Fin N)).corner e he) φ.toRingHom φ.injective
    have hall := (GroupApproximation.ChainCore.ChainCoreClosures.coreRingReflectionStatement_holds _
      (restrictHomeo T hY) (ZMod 2)).2.2.1 hLEF_Y
    have hmaps : Set.MapsTo
        (Subtype.val : returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) → X)
        (Dynamics.chainRecurrentSet (restrictHomeo T hY)) (Dynamics.chainRecurrentSet T) :=
      Dynamics.mapsTo_chainRecurrentSet continuous_subtype_val (fun _ => rfl)
    exact hmaps (hall ⟨x, hx⟩)
  refine ⟨hsub, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, hsub (subset_returnSaturation y hy)⟩

/-! ## tex 1749–1750: the return transient ideal -/

/-- **tex 1749–1750**, "The return transient ideal is therefore $J=p_CIp_C$": under the return ring
isomorphism `R_{S_C} ≅ P_C = p_C R_X p_C`, an element lies in the transient ideal of the return system
`(C, S_C)` exactly when its image lies in `p_C I p_C`. -/
def PrintedReturnTransientIdeal : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [TotallyDisconnectedSpace X] [Nonempty X]
    (T : X ≃ₜ X) (r : ℕ) (C : Set X) (hC : IsReturnSection T r C) [CompactSpace C]
    (k : Type) [Field k] [Finite k] (c : ClopenCrossedProduct (firstReturnHomeomorph hC) k),
    (∃ a ∈ coreTransientIdeal T k,
        ((returnRingEquiv k hC c : ReturnCorner k hC) : ClopenCrossedProduct T k) =
          returnP k hC * a * returnP k hC) ↔
      c ∈ coreTransientIdeal (firstReturnHomeomorph hC) k

theorem printedReturnTransientIdeal_closed : PrintedReturnTransientIdeal := by
  intro X _ _ _ _ T r C hC _ k _ _ c
  constructor
  · rintro ⟨a, ha, hca⟩
    have hmem : ((returnRingHom k hC c : ReturnCorner k hC) : ClopenCrossedProduct T k) ∈
        coreTransientIdeal T k := by
      rw [← returnRingEquiv_apply, hca]
      exact (coreTransientIdeal T k).mul_mem_right _ _ ((coreTransientIdeal T k).mul_mem_left _ _ ha)
    refine (mem_transientIdeal_iff_forall_coeff _ _ _).2 fun g y hy => ?_
    have hyT : (y : X) ∈ Dynamics.chainRecurrentSet T := coe_mem_chainRecurrentSet_of_firstReturn hC hy
    have hmem' : ((returnRingHom k hC (c * ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k ^
        (-toAdd g) : (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k)) : ReturnCorner k hC) :
            ClopenCrossedProduct T k) ∈ coreTransientIdeal T k := by
      rw [map_mul, coe_corner_mul]
      exact (coreTransientIdeal T k).mul_mem_right _ _ hmem
    have h0 := (mem_transientIdeal_iff_forall_coeff _ _ _).1 hmem' 1 (y : X) hyT
    rw [coeff_one_coe_returnRingHom, RingEquiv.symm_apply_apply,
      clopenExtendByZero_apply_of_mem k hC.isClopen _ y.2, clopen_coeff_mul_unit_zpow_neg_toAdd] at h0
    exact h0
  · intro hc
    have hsingle : ∀ g : Multiplicative ℤ, ((returnRingHom k hC
        (SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff c g)) : ReturnCorner k hC) :
          ClopenCrossedProduct T k) ∈ coreTransientIdeal T k := by
      intro g
      have hsplit : (SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff c g) :
          ClopenCrossedProduct (firstReturnHomeomorph hC) k) =
          ClopenCrossedProduct.coeff (firstReturnHomeomorph hC) k
              ((ClopenCoeff.of (firstReturnHomeomorph hC) k).symm (SkewMonoidAlgebra.coeff c g)) *
            ((ClopenCrossedProduct.unit (firstReturnHomeomorph hC) k ^ toAdd g :
              (ClopenCrossedProduct (firstReturnHomeomorph hC) k)ˣ) :
                ClopenCrossedProduct (firstReturnHomeomorph hC) k) := by
        rw [Pestov91.CrossedProduct.val_unit_zpow, ClopenCrossedProduct.coeff_apply,
          RingEquiv.apply_symm_apply, Pestov91.CrossedProduct.C_mul_single, mul_one, ofAdd_toAdd]
      rw [hsplit, map_mul, coe_corner_mul, coe_returnRingHom_coeff]
      refine (coreTransientIdeal T k).mul_mem_right _ _ ?_
      classical
      refine (mem_transientIdeal_iff_forall_coeff _ _ _).2 fun g' y hy => ?_
      rw [ClopenCrossedProduct.coeff_apply, Pestov91.CrossedProduct.C_apply,
        SkewMonoidAlgebra.coeff_single_apply]
      split_ifs
      · rw [RingEquiv.symm_apply_apply]
        by_cases hyC : y ∈ C
        · rw [clopenExtendByZero_apply_of_mem k hC.isClopen _ hyC]
          exact (mem_transientIdeal_iff_forall_coeff _ _ _).1 hc g ⟨y, hyC⟩
            (mem_chainRecurrentSet_firstReturn_of_pieces
              GroupApproximation.ChainCore.ChainCoreClosures.coreRingReflectionStatement_holds
              GroupApproximation.ChainCore.coreModelsLEFStatement T hC hyC hy)
        · exact clopenExtendByZero_apply_of_notMem k hC.isClopen _ hyC
      · rw [map_zero, LocallyConstant.zero_apply]
    have hsum := Finset.sum_induction (s := c.support)
      (fun g => (SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff c g) :
        ClopenCrossedProduct (firstReturnHomeomorph hC) k))
      (fun z : ClopenCrossedProduct (firstReturnHomeomorph hC) k =>
        ((returnRingHom k hC z : ReturnCorner k hC) : ClopenCrossedProduct T k) ∈
          coreTransientIdeal T k)
      (fun a b ha hb => by
        simp only [map_add, coe_corner_add]
        exact (coreTransientIdeal T k).add_mem ha hb)
      (by
        simp only [map_zero, coe_corner_zero]
        exact (coreTransientIdeal T k).zero_mem)
      (fun g _ => hsingle g)
    have hdec : ∑ g ∈ c.support, (SkewMonoidAlgebra.single g (SkewMonoidAlgebra.coeff c g) :
        ClopenCrossedProduct (firstReturnHomeomorph hC) k) = c :=
      (SkewMonoidAlgebra.sum_def' c SkewMonoidAlgebra.single).symm.trans (SkewMonoidAlgebra.sum_single c)
    rw [hdec] at hsum
    refine ⟨((returnRingEquiv k hC c : ReturnCorner k hC) : ClopenCrossedProduct T k), hsum, ?_⟩
    rw [(returnRingEquiv k hC c).2.1, (returnRingEquiv k hC c).2.2]

end GroupApproximation.ChainCore.DynamicRankBudget

/-! ### Audit -/

#audit_axioms GroupApproximation.ChainCore.DynamicRankBudget.exists_corner_matrix_returnSaturation
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedInducedCoreCorner_closed
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedCoreSaturationLEF_closed
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedCoreSaturationRecurrent_closed
#audit_closed_axioms GroupApproximation.ChainCore.DynamicRankBudget.printedReturnTransientIdeal_closed
