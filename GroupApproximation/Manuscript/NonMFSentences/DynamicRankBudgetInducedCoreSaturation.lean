import GroupApproximation.Manuscript.NonMFSentences.DynamicRankBudgetInducedCoreReverse
import GroupApproximation.Dynamics.ReturnSaturation
import GroupApproximation.Dynamics.ChainCoreGeneralFactor
import GroupApproximation.Meta.AxiomGuard

/-!
# `cor:dynamic-rank-budget`: the induced core lies in the core, by saturation

`non_mf_groups_exist.tex`, proof of Corollary `cor:dynamic-rank-budget`
(`\label{cor:dynamic-rank-budget}`), tex 1743–1750:

> The induced core is $C\cap Y$.  Indeed its return ring is a corner
> of the LEF ring $R_Y$, so it lies in the induced chain-recurrent core.
> Conversely, saturating that core through the finite towers gives a
> closed invariant subsystem whose ring is a corner of a matrix ring
> over an LEF ring, hence LEF.  Theorem~\ref{thm:core-ring-reflection}
> applied to this subsystem makes every one of its points chain recurrent
> in $X$, proving the reverse inclusion.

This module proves `CR(S_C) ⊆ C ∩ Y` along the printed saturation route.  ct-rank-budget's
`coe_mem_chainRecurrentSet_of_firstReturn` proves the same inclusion by a direct chain argument.

* `coe_mem_chainRecurrentSet_of_firstReturn_of_pieces`, over `CoreRingReflectionStatement` and
  `CoreModelsLEFStatement`.
  - Let `Z = CR(S_C)`, and let `Y' = returnSaturation T C Z` be its saturation through the towers, a
    closed invariant subsystem (`Dynamics/ReturnSaturation`).
  - `C ∩ Y'` is a return section of `T|_{Y'}` whose first-return system is conjugate to `(Z, S_C|_Z)`.
    So its return ring embeds in the LEF ring `R_Z` (`CoreModelsLEFStatement` for `(C, S_C)`,
    `comap_injective`), and is LEF.
  - The return corner `P_{C∩Y'}` is isomorphic to that return ring (`returnRingEquiv`).
    `R_{Y'} ≅ E M_{2r-1}(P_{C∩Y'}) E` (`ReturnTowerUnits.cornerEquiv`) is a corner of a matrix ring over
    an LEF ring, hence LEF.
  - Theorem `thm:core-ring-reflection` for `(Y', T|_{Y'})` makes every point chain recurrent in `X`.
* `image_chainRecurrentSet_firstReturn_printed`: `CR(S_C) = C ∩ CR(T)`, with both inclusions along the
  printed route, over the same two pieces.
-/

namespace GroupApproximation.ChainCore.DynamicRankBudget

open MFQuotientUnits ClopenCrossedProduct

/-- **`CR(S_C) ⊆ C ∩ Y`** (tex 1745–1749), along the printed saturation route, over Lemma
`lem:chain-core-models` ("$R_Y$ is LEF") and Theorem `thm:core-ring-reflection`. -/
theorem coe_mem_chainRecurrentSet_of_firstReturn_of_pieces (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) {y : C}
    (hy : y ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :
    (y : X) ∈ Dynamics.chainRecurrentSet T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : 1 ≤ r := by
    obtain ⟨j, hj, -⟩ := hC.exists_mem_image (y : X)
    have := abs_nonneg j
    omega
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hC.isClopen.isClosed.isCompact
  haveI : Nonempty C := ⟨y⟩
  have hZ : ∀ z : C, firstReturnHomeomorph hC z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) ↔
      z ∈ Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) :=
    fun z => Dynamics.apply_mem_chainRecurrentSet_iff (firstReturnHomeomorph hC)
  have hZc : IsClosed (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    Dynamics.isClosed_chainRecurrentSet (firstReturnHomeomorph hC).continuous
  have hY : T '' returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) =
      returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) :=
    image_returnSaturation _
  have hYc := isClosed_returnSaturation hC hZ hZc
  haveI : CompactSpace
      (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))) :=
    isCompact_iff_compactSpace.mp hYc.isCompact
  haveI : Nonempty
      (returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC))) :=
    ⟨⟨(y : X), subset_returnSaturation y hy⟩⟩
  have hC' := isReturnSection_restrict hC hY
  -- The first-return system of `C ∩ Y'` is a factor of the induced core `(Z, S_C|_Z)`.
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
  -- LEF climbs from the induced core to the saturated subsystem.
  have hLEF_S : Pestov91.IsLEFRing (ClopenCrossedProduct (firstReturnHomeomorph hC') (ZMod 2)) :=
    Pestov91.IsLEFRing.of_injective (hModels C (firstReturnHomeomorph hC) (ZMod 2))
      (comap (ZMod 2) π hπ) (comap_injective (ZMod 2) π hπ hsurj)
  have hLEF_P : Pestov91.IsLEFRing (ReturnCorner (ZMod 2) hC') :=
    Pestov91.IsLEFRing.of_injective hLEF_S (returnRingEquiv (ZMod 2) hC').symm.toRingHom
      (returnRingEquiv (ZMod 2) hC').symm.injective
  have hLEF_base : Pestov91.IsLEFRing (returnTowerUnits (ZMod 2) hC' hr).Base := hLEF_P
  have hLEF_E := (hLEF_base.matrix (Fin (2 * r - 1))).corner
    ((returnTowerUnits (ZMod 2) hC' hr).toMatrix 1)
    (returnTowerUnits (ZMod 2) hC' hr).isIdempotentElem_toMatrix_one
  have hLEF_Y : Pestov91.IsLEFRing (ClopenCrossedProduct (restrictHomeo T hY) (ZMod 2)) :=
    Pestov91.IsLEFRing.of_injective hLEF_E (returnTowerUnits (ZMod 2) hC' hr).cornerEquiv.toRingHom
      (returnTowerUnits (ZMod 2) hC' hr).cornerEquiv.injective
  -- Core-ring reflection for the saturated subsystem.
  have hall := (hRefl _ (restrictHomeo T hY) (ZMod 2)).2.2.1 hLEF_Y
  have hmaps : Set.MapsTo
      (Subtype.val : returnSaturation T C (Dynamics.chainRecurrentSet (firstReturnHomeomorph hC)) → X)
      (Dynamics.chainRecurrentSet (restrictHomeo T hY)) (Dynamics.chainRecurrentSet T) :=
    Dynamics.mapsTo_chainRecurrentSet continuous_subtype_val (fun _ => rfl)
  exact hmaps (hall ⟨(y : X), subset_returnSaturation y hy⟩)

/-- **The induced core is `C ∩ Y`** (tex 1743–1750): `CR(S_C) = C ∩ CR(T)`, with both inclusions
along the printed route, over Lemma `lem:chain-core-models` and Theorem `thm:core-ring-reflection`. -/
theorem image_chainRecurrentSet_firstReturn_printed (hRefl : CoreRingReflectionStatement)
    (hModels : CoreModelsLEFStatement) {X : Type} [MetricSpace X] [CompactSpace X]
    [TotallyDisconnectedSpace X] [Nonempty X] (T : X ≃ₜ X) {r : ℕ} {C : Set X}
    (hC : IsReturnSection T r C) :
    Subtype.val '' Dynamics.chainRecurrentSet (firstReturnHomeomorph hC) =
      C ∩ Dynamics.chainRecurrentSet T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, coe_mem_chainRecurrentSet_of_firstReturn_of_pieces hRefl hModels T hC hy⟩
  · rintro ⟨hxC, hxY⟩
    exact ⟨⟨x, hxC⟩, mem_chainRecurrentSet_firstReturn_of_pieces hRefl hModels T hC hxC hxY, rfl⟩

end GroupApproximation.ChainCore.DynamicRankBudget

open GroupApproximation.ChainCore.DynamicRankBudget

#audit_axioms coe_mem_chainRecurrentSet_of_firstReturn_of_pieces
#audit_axioms image_chainRecurrentSet_firstReturn_printed
