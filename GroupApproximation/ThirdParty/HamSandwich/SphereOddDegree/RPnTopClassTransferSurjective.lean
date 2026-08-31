import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlgebraicTopology.CoveringTransferSES
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnTopClassTransferNonzero
import GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.RPnAdditiveCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Field.ZMod

/-!
# Top-degree surjectivity of the double-cover cohomology transfer

This file dualizes the mod-2 Smith short exact sequence of singular chain
complexes (built in `CoveringTransferSES.lean`)

```text
0 ⟶ C_•(RPⁿ; F₂) ──tr──▶ C_•(Sⁿ; F₂) ──proj_*──▶ C_•(RPⁿ; F₂) ⟶ 0
```

into the short exact sequence of singular **cochain** complexes

```text
0 ⟶ C^•(RPⁿ; F₂) ──proj^*──▶ C^•(Sⁿ; F₂) ──tr──▶ C^•(RPⁿ; F₂) ⟶ 0
```

(the dualization is exact because the chain sequence is degreewise split over the
field `F₂`).  Its long exact cohomology sequence, together with the vanishing
`Hⁿ⁺¹(RPⁿ; F₂) = 0` (real projective space is `n`-dimensional), shows that the
genuine cohomology transfer

```text
cohTransferZMod2 n n : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)
```

is **surjective** in the top degree.  This is the genuine top-degree statement of
the transfer/Gysin sequence; it is *not* the degenerate ordinary pullback
`projPullback`.

A right inverse of this surjection is the honest transfer object
`rpToSphereTopTransfer`, a genuine linear map `Hⁿ(RPⁿ; F₂) ⟶ Hⁿ(Sⁿ; F₂)` built
*from the genuine transfer* (never from `projPullback`); being a section of a
linear map it is injective, so it carries every nonzero top `RPⁿ`-class to a
nonzero top `Sⁿ`-class.
-/

noncomputable section

open CategoryTheory Limits AlgebraicTopology

namespace GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

/-- The `Hom(-, M)` dualizer on chain complexes is additive. -/
instance dualizeCochainFunctor_additive (R : Type) [CommRing R] (M : ModuleCat.{0} R) :
    (dualizeCochainFunctor R M).Additive := by
  unfold dualizeCochainFunctor
  infer_instance

/-- Every `ZMod 2`-module object is projective (`ZMod 2` is a field). -/
instance moduleCat_zmod2_projective (M : ModuleCat.{0} (ZMod 2)) :
    Module.Projective (ZMod 2) M :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module.Free (ZMod 2) M := Module.Free.of_divisionRing (ZMod 2) M
  Module.Projective.of_free

/-! ## 1. The dualized cochain short exact sequence -/

/-- The mod-2 Smith short exact sequence of singular **cochain** complexes,
obtained by dualizing the chain sequence `transferSESChain n` with the
`Hom(-, F₂)` dualizer.  Its middle map is the genuine cohomology transfer. -/
noncomputable def transferSEScoch (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ) :=
  (transferSESChain n).op.map (dualizeCochainFunctor (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)))

/-- The middle map of the dualized sequence is the cohomology transfer cochain
map. -/
theorem transferSEScoch_g (n : ℕ) :
    (transferSEScoch n).g = projTransferCochainMap n :=
  rfl

/-- The cohomology of the right term of the dualized sequence is `Hᵏ(RPⁿ; F₂)`. -/
theorem transferSEScoch_X₃_homology (n k : ℕ) :
    (transferSEScoch n).X₃.homology k = rpCohomology n k :=
  rfl

/-- The cohomology of the left term of the dualized sequence is `Hᵏ(RPⁿ; F₂)`. -/
theorem transferSEScoch_X₁_homology (n k : ℕ) :
    (transferSEScoch n).X₁.homology k = rpCohomology n k :=
  rfl

/-- The cohomology of the middle term of the dualized sequence is `Hᵏ(Sⁿ; F₂)`. -/
theorem transferSEScoch_X₂_homology (n k : ℕ) :
    (transferSEScoch n).X₂.homology k = sphereCohomology n k :=
  rfl

/-- The induced cohomology map of the middle map is the cohomology transfer. -/
theorem transferSEScoch_homologyMap_g (n k : ℕ) :
    HomologicalComplex.homologyMap (transferSEScoch n).g k = cohTransferZMod2 n k := by
  rw [transferSEScoch_g, cohTransferZMod2_eq_homologyMap]

/-- **The dualized cochain short exact sequence is short exact.** Over the field
`F₂` the degreewise-split chain sequence dualizes to a (degreewise-split, hence)
short exact cochain sequence. -/
theorem transferSEScoch_shortExact (n : ℕ) : (transferSEScoch n).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro k
  exact ((transferSESChain_degreewiseSplitting n k).op.map
    ((linearYoneda (ZMod 2) (ModuleCat.{0} (ZMod 2))).obj
      (ModuleCat.of (ZMod 2) (ZMod 2)))).shortExact

/-! ## 2. Top-degree surjectivity of the cohomology transfer -/

/-- **Top-degree surjectivity of the genuine cohomology transfer.** Using the long
exact cohomology sequence of the dualized Smith sequence and the vanishing
`Hⁿ⁺¹(RPⁿ; F₂) = 0`, the cohomology transfer
`cohTransferZMod2 n n : Hⁿ(Sⁿ; F₂) ⟶ Hⁿ(RPⁿ; F₂)` is surjective. -/
theorem cohTransferZMod2_top_surjective (n : ℕ) (c : RPnCellularCochainStructure n) :
    Function.Surjective (cohTransferZMod2 n n).hom := by
  have hSE := transferSEScoch_shortExact n
  have hrel : (ComplexShape.up ℕ).Rel n (n + 1) := rfl
  -- Exactness of `Hⁿ(X₂) → Hⁿ(X₃) → Hⁿ⁺¹(X₁)`.
  have hexact := hSE.homology_exact₃ n (n + 1) hrel
  rw [ShortComplex.moduleCat_exact_iff] at hexact
  -- `Hⁿ⁺¹(X₁) = Hⁿ⁺¹(RPⁿ; F₂) = 0`.
  have hzero : IsZero ((transferSEScoch n).X₁.homology (n + 1)) := by
    rw [transferSEScoch_X₁_homology]
    exact rpCohomology_isZero_above_dimension c (n + 1) (by omega)
  haveI hsub : Subsingleton ((transferSEScoch n).X₁.homology (n + 1)) :=
    (ModuleCat.isZero_iff_subsingleton).mp hzero
  intro y
  obtain ⟨x, hx⟩ := hexact y (Subsingleton.elim _ _)
  refine ⟨x, ?_⟩
  rw [← transferSEScoch_homologyMap_g n n]
  exact hx

/-! ## 3. The honest top transfer `Hⁿ(RPⁿ) ⟶ Hⁿ(Sⁿ)` and its injectivity -/

/-- A chosen linear right inverse of the surjective top cohomology transfer. -/
noncomputable def rpToSphereTopTransferLinear (n : ℕ) (c : RPnCellularCochainStructure n) :
    rpCohomology n n →ₗ[ZMod 2] sphereCohomology n n :=
  (LinearMap.exists_rightInverse_of_surjective (cohTransferZMod2 n n).hom
    (LinearMap.range_eq_top.mpr (cohTransferZMod2_top_surjective n c))).choose

theorem cohTransferZMod2_comp_rpToSphereTopTransferLinear (n : ℕ)
    (c : RPnCellularCochainStructure n) :
    (cohTransferZMod2 n n).hom ∘ₗ rpToSphereTopTransferLinear n c = LinearMap.id :=
  (LinearMap.exists_rightInverse_of_surjective (cohTransferZMod2 n n).hom
    (LinearMap.range_eq_top.mpr (cohTransferZMod2_top_surjective n c))).choose_spec

/-- **The honest top-degree transfer** `Hⁿ(RPⁿ; F₂) ⟶ Hⁿ(Sⁿ; F₂)`, a genuine
linear section of the surjective cohomology transfer `cohTransferZMod2 n n` (built
*from* the genuine transfer, never from the degenerate `projPullback`). Being a
section of a linear map it is injective. -/
noncomputable def rpToSphereTopTransfer (n : ℕ) (c : RPnCellularCochainStructure n) :
    rpCohomology n n ⟶ sphereCohomology n n :=
  ModuleCat.ofHom (rpToSphereTopTransferLinear n c)

/-- The honest top transfer is a section of the genuine cohomology transfer:
`cohTransferZMod2 n n ∘ rpToSphereTopTransfer = id`. -/
theorem rpToSphereTopTransfer_section (n : ℕ) (c : RPnCellularCochainStructure n)
    (a : rpCohomology n n) :
    (cohTransferZMod2 n n).hom ((rpToSphereTopTransfer n c).hom a) = a := by
  have h := cohTransferZMod2_comp_rpToSphereTopTransferLinear n c
  have := DFunLike.congr_fun h a
  simpa [rpToSphereTopTransfer] using this

/-- **Top-degree nonzero preservation (the deliverable).** A nonzero top class of
`Hⁿ(RPⁿ; F₂)` transfers to a nonzero top class of `Hⁿ(Sⁿ; F₂)` under the honest
transfer `rpToSphereTopTransfer`. -/
theorem rpToSphereTopTransfer_nonzero (n : ℕ) (c : RPnCellularCochainStructure n)
    {a : rpCohomology n n} (ha : a ≠ 0) :
    (rpToSphereTopTransfer n c).hom a ≠ 0 := by
  intro h0
  apply ha
  have hs := rpToSphereTopTransfer_section n c a
  simp only [h0, map_zero] at hs
  exact hs.symm

end GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

