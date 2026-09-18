import GroupApproximation.KTheory.K0Basic
import GroupApproximation.KTheory.K1Functorial
import GroupApproximation.Analysis.CStarKOneWhitehead
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# K-theory of non-unital C⋆-algebras: the interface

Lane `TWWSch3d3a`, work order `WO-TWWSchafhauser-3d3-1`.
Manuscript: `non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378). That
theorem cites Tikuisis--White--Winter, Ann. of Math. 185 (2017), Theorem A, through
C. Schafhauser, J. reine angew. Math. 759 (2020), §4--5. There, the trace-kernel ideal `J`
is non-unital, and the argument uses `K₁(J) = 0` and the divisibility of `K₀(J)`. This file
fixes the groups `K₀(J)` and `K₁(J)` for a non-unital C⋆-algebra `J`, together with their
functoriality. The definitions follow M. Rørdam, F. Larsen, N. Laustsen, *An introduction to
K-theory for C⋆-algebras*, Definition 4.2.1 and §8.1.

* `scalarHom J : J⁺ →⋆ₐ[ℂ] ℂ` is the scalar part `x ↦ x.fst` of the unitization;
* `KZeroN J` is `ker (K₀(J⁺) → K₀(ℂ))` (RLL Definition 4.2.1), built on the projection-picture
  `K₀` of `GroupApproximation.KTheory.KZero`;
* `KOneN J` is `K₁(J⁺) = colim_n U_n(J⁺)/U_n(J⁺)₀` (RLL §8.1), written additively. We use the
  sequential-colimit `K₁` of `GroupApproximation.KOne`, where `J⁺` carries its spectral order;
* `KZeroN.map`, `KOneN.map` are the maps induced by `φ : J →⋆ₙₐ[ℂ] J'` through
  `Unitization.starMap φ`. The lemmas `map_id` and `map_comp` state functoriality.

`KOneN J` only needs `[NonUnitalCStarAlgebra J]`. The order on `J⁺` that `KOne` needs is
`CStarAlgebra.spectralOrder`. It is a local instance here and is exported as the definitions
`unitizationOrder` and `unitizationStarOrderedRing`. When `J` already has a C⋆-order, Mathlib's
order on `J⁺` is the same spectral order (by definition), so no diamond arises.
-/

namespace GroupApproximation
namespace Full
namespace TWWSchafhauser

noncomputable section

/-! ### Unital star algebra maps as star ring maps -/

section StarRingHomOf

variable {X Y : Type*} [Semiring X] [Algebra ℂ X] [StarRing X] [Semiring Y] [Algebra ℂ Y]
  [StarRing Y]

/-- The underlying non-unital star ring homomorphism of a star algebra homomorphism. -/
def starRingHomOf (φ : X →⋆ₐ[ℂ] Y) : X →⋆ₙ+* Y where
  toFun := φ
  map_mul' := map_mul φ
  map_zero' := map_zero φ
  map_add' := map_add φ
  map_star' := map_star φ

theorem starRingHomOf_apply (φ : X →⋆ₐ[ℂ] Y) (x : X) : starRingHomOf φ x = φ x :=
  rfl

end StarRingHomOf

/-! ### The scalar part of the unitization -/

section Scalar

variable (J : Type) [NonUnitalCStarAlgebra J]

/-- The scalar part `J⁺ → ℂ`, `x ↦ x.fst`, of the unitization. This is the lift of the zero map
`J → ℂ` (RLL §4.1). -/
def scalarHom : Unitization ℂ J →⋆ₐ[ℂ] ℂ :=
  Unitization.starLift (0 : J →⋆ₙₐ[ℂ] ℂ)

variable {J}

theorem scalarHom_apply (x : Unitization ℂ J) : scalarHom J x = x.fst := by
  show algebraMap ℂ ℂ x.fst + (0 : J →⋆ₙₐ[ℂ] ℂ) x.snd = x.fst
  rw [NonUnitalStarAlgHom.zero_apply, add_zero, Algebra.algebraMap_self_apply]

theorem scalarHom_starMap {J' : Type} [NonUnitalCStarAlgebra J'] (φ : J →⋆ₙₐ[ℂ] J')
    (x : Unitization ℂ J) : scalarHom J' (Unitization.starMap φ x) = scalarHom J x := by
  rw [scalarHom_apply, scalarHom_apply]
  show ((Unitization.inl x.fst : Unitization ℂ J') + (φ x.snd : Unitization ℂ J')).fst = x.fst
  rw [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]

/-- The unitized map commutes with the scalar parts. -/
theorem scalarHom_comp_starMap {J' : Type} [NonUnitalCStarAlgebra J'] (φ : J →⋆ₙₐ[ℂ] J') :
    (scalarHom J').comp (Unitization.starMap φ) = scalarHom J :=
  StarAlgHom.ext fun x => scalarHom_starMap φ x

end Scalar

/-! ### `K₀` of a non-unital C⋆-algebra -/

section KZero

variable {J J' J'' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']
  [NonUnitalCStarAlgebra J'']

variable (J) in
/-- **`K₀` of a non-unital C⋆-algebra** (RLL Definition 4.2.1). It is the kernel of the map
`K₀(J⁺) → K₀(ℂ)` induced by the scalar part `J⁺ → ℂ`. -/
abbrev KZeroN : Type :=
  ↥(AddMonoidHom.ker (KTheory.KZero.map (starRingHomOf (scalarHom J))))

/-- The inclusion `K₀(J) → K₀(J⁺)`. -/
def KZeroN.incl : KZeroN J →+ KTheory.KZero (Unitization ℂ J) :=
  AddSubgroup.subtype _

theorem KZeroN.incl_apply (x : KZeroN J) : KZeroN.incl x = x.1 :=
  rfl

theorem KZeroN.incl_injective : Function.Injective (KZeroN.incl (J := J)) :=
  Subtype.val_injective

/-- The map `K₀(J⁺) → K₀(J'⁺)` induced by `φ` preserves the kernels of the scalar parts. -/
theorem KZeroN.map_mem (φ : J →⋆ₙₐ[ℂ] J') {x : KTheory.KZero (Unitization ℂ J)}
    (hx : x ∈ AddMonoidHom.ker (KTheory.KZero.map (starRingHomOf (scalarHom J)))) :
    KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x ∈
      AddMonoidHom.ker (KTheory.KZero.map (starRingHomOf (scalarHom J'))) := by
  rw [AddMonoidHom.mem_ker] at hx ⊢
  have h : (starRingHomOf (scalarHom J')).comp (starRingHomOf (Unitization.starMap φ)) =
      starRingHomOf (scalarHom J) :=
    NonUnitalStarRingHom.ext fun y => scalarHom_starMap φ y
  calc KTheory.KZero.map (starRingHomOf (scalarHom J'))
        (KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x)
      = KTheory.KZero.map ((starRingHomOf (scalarHom J')).comp
          (starRingHomOf (Unitization.starMap φ))) x :=
        (DFunLike.congr_fun (KTheory.KZero.map_comp (starRingHomOf (scalarHom J'))
          (starRingHomOf (Unitization.starMap φ))) x).symm
    _ = KTheory.KZero.map (starRingHomOf (scalarHom J)) x := by rw [h]
    _ = 0 := hx

/-- **Functoriality of `K₀`** for non-unital star homomorphisms (RLL §4.2). -/
def KZeroN.map (φ : J →⋆ₙₐ[ℂ] J') : KZeroN J →+ KZeroN J' where
  toFun x := ⟨KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x.1, KZeroN.map_mem φ x.2⟩
  map_zero' := Subtype.ext
    (show KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) 0 = 0 from map_zero _)
  map_add' x y := Subtype.ext
    (show KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) (x.1 + y.1) =
        KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x.1 +
          KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) y.1 from
      map_add _ _ _)

theorem KZeroN.map_apply_coe (φ : J →⋆ₙₐ[ℂ] J') (x : KZeroN J) :
    (KZeroN.map φ x).1 = KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x.1 :=
  rfl

theorem KZeroN.incl_map (φ : J →⋆ₙₐ[ℂ] J') (x : KZeroN J) :
    KZeroN.incl (KZeroN.map φ x) = KTheory.KZero.map (starRingHomOf (Unitization.starMap φ))
      (KZeroN.incl x) :=
  rfl

/-- `K₀` sends the identity to the identity. -/
theorem KZeroN.map_id : KZeroN.map (NonUnitalStarAlgHom.id ℂ J) = AddMonoidHom.id (KZeroN J) := by
  have h : starRingHomOf (Unitization.starMap (NonUnitalStarAlgHom.id ℂ J)) =
      NonUnitalStarRingHom.id (Unitization ℂ J) :=
    NonUnitalStarRingHom.ext fun y =>
      DFunLike.congr_fun (Unitization.starMap_id (R := ℂ) (B := J)) y
  refine AddMonoidHom.ext fun x => Subtype.ext ?_
  show KTheory.KZero.map (starRingHomOf (Unitization.starMap (NonUnitalStarAlgHom.id ℂ J))) x.1 =
    x.1
  calc KTheory.KZero.map (starRingHomOf (Unitization.starMap (NonUnitalStarAlgHom.id ℂ J))) x.1
      = KTheory.KZero.map (NonUnitalStarRingHom.id (Unitization ℂ J)) x.1 := by rw [h]
    _ = x.1 := DFunLike.congr_fun (KTheory.KZero.map_id (A := Unitization ℂ J)) x.1

/-- `K₀` sends composites to composites. -/
theorem KZeroN.map_comp (ψ : J' →⋆ₙₐ[ℂ] J'') (φ : J →⋆ₙₐ[ℂ] J') :
    KZeroN.map (ψ.comp φ) = (KZeroN.map ψ).comp (KZeroN.map φ) := by
  have h : starRingHomOf (Unitization.starMap (ψ.comp φ)) =
      (starRingHomOf (Unitization.starMap ψ)).comp (starRingHomOf (Unitization.starMap φ)) :=
    NonUnitalStarRingHom.ext fun y =>
      DFunLike.congr_fun (Unitization.starMap_comp (φ := φ) (ψ := ψ)) y
  refine AddMonoidHom.ext fun x => Subtype.ext ?_
  show KTheory.KZero.map (starRingHomOf (Unitization.starMap (ψ.comp φ))) x.1 =
    KTheory.KZero.map (starRingHomOf (Unitization.starMap ψ))
      (KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x.1)
  calc KTheory.KZero.map (starRingHomOf (Unitization.starMap (ψ.comp φ))) x.1
      = KTheory.KZero.map ((starRingHomOf (Unitization.starMap ψ)).comp
          (starRingHomOf (Unitization.starMap φ))) x.1 := by rw [h]
    _ = KTheory.KZero.map (starRingHomOf (Unitization.starMap ψ))
          (KTheory.KZero.map (starRingHomOf (Unitization.starMap φ)) x.1) :=
        DFunLike.congr_fun (KTheory.KZero.map_comp (starRingHomOf (Unitization.starMap ψ))
          (starRingHomOf (Unitization.starMap φ))) x.1

end KZero

/-! ### The spectral order on the unitization -/

section Order

variable (J : Type) [NonUnitalCStarAlgebra J]

/-- The spectral order on the unitization `J⁺`. It is used as a local instance, so that `K₁(J⁺)`
can be formed without an order on `J`. It agrees by definition with Mathlib's order on `J⁺`
when `J` has a C⋆-order. -/
@[reducible] def unitizationOrder : PartialOrder (Unitization ℂ J) :=
  CStarAlgebra.spectralOrder (Unitization ℂ J)

attribute [local instance] unitizationOrder

/-- The unitization, with its spectral order, is a star-ordered ring. -/
theorem unitizationStarOrderedRing : StarOrderedRing (Unitization ℂ J) :=
  CStarAlgebra.spectralOrderedRing (Unitization ℂ J)

end Order

/-! ### `K₁` of a non-unital C⋆-algebra -/

section KOne

attribute [local instance] unitizationOrder unitizationStarOrderedRing

variable {J J' J'' : Type} [NonUnitalCStarAlgebra J] [NonUnitalCStarAlgebra J']
  [NonUnitalCStarAlgebra J'']

variable (J) in
/-- **`K₁` of a non-unital C⋆-algebra** (RLL §8.1), `K₁(J) = K₁(J⁺)`. This is the colimit of
`U_n(J⁺)/U_n(J⁺)₀`, written additively. `J⁺` carries its spectral order `unitizationOrder`. -/
def KOneN : Type :=
  Additive (KOne (Unitization ℂ J))

variable (J) in
instance KOneN.instAddCommGroup : AddCommGroup (KOneN J) :=
  inferInstanceAs (AddCommGroup (Additive (KOne (Unitization ℂ J))))

/-- The identification of `K₁(J⁺)` (multiplicative) with `K₁(J)` (additive). -/
def KOneN.ofMul : KOne (Unitization ℂ J) ≃ KOneN J :=
  Additive.ofMul

theorem KOneN.ofMul_mul (a b : KOne (Unitization ℂ J)) :
    KOneN.ofMul (a * b) = KOneN.ofMul a + KOneN.ofMul b :=
  rfl

theorem KOneN.ofMul_one : KOneN.ofMul (1 : KOne (Unitization ℂ J)) = 0 :=
  rfl

/-- The class `[v] ∈ K₁(J)` of a unitary `v ∈ U_n(J⁺)`. -/
def KOneN.mk (n : ℕ) (v : unitary (CStarMat n (Unitization ℂ J))) : KOneN J :=
  KOneN.ofMul (kOneIota (Unitization ℂ J) n (QuotientGroup.mk v))

/-- Every element of `K₁(J)` is the class of a unitary over `J⁺`. -/
theorem KOneN.exists_mk (x : KOneN J) :
    ∃ (n : ℕ) (v : unitary (CStarMat n (Unitization ℂ J))), x = KOneN.mk n v := by
  obtain ⟨n, y, hy⟩ := (kOneTower (Unitization ℂ J)).exists_iota ((KOneN.ofMul (J := J)).symm x)
  have hx : x = KOneN.ofMul (kOneIota (Unitization ℂ J) n y) :=
    (KOneN.ofMul (J := J)).symm_apply_eq.mp hy
  revert hx
  refine QuotientGroup.induction_on y fun v hv => ?_
  exact ⟨n, v, hv⟩

/-- **Functoriality of `K₁`** for non-unital star homomorphisms (RLL §8.1). It is the map
induced on `K₁(J⁺)` by `Unitization.starMap φ`. -/
def KOneN.map (φ : J →⋆ₙₐ[ℂ] J') : KOneN J →+ KOneN J' :=
  MonoidHom.toAdditive (KOne.map (Unitization.starMap φ))

theorem KOneN.map_ofMul (φ : J →⋆ₙₐ[ℂ] J') (a : KOne (Unitization ℂ J)) :
    KOneN.map φ (KOneN.ofMul a) = KOneN.ofMul (KOne.map (Unitization.starMap φ) a) :=
  rfl

theorem KOneN.map_mk (φ : J →⋆ₙₐ[ℂ] J') (n : ℕ) (v : unitary (CStarMat n (Unitization ℂ J))) :
    KOneN.map φ (KOneN.mk n v) = KOneN.mk n (matMapUnitary (Unitization.starMap φ) n v) :=
  rfl

/-- `K₁` sends the identity to the identity. -/
theorem KOneN.map_id : KOneN.map (NonUnitalStarAlgHom.id ℂ J) = AddMonoidHom.id (KOneN J) := by
  have h : KOne.map (Unitization.starMap (NonUnitalStarAlgHom.id ℂ J)) =
      MonoidHom.id (KOne (Unitization ℂ J)) := by
    rw [Unitization.starMap_id]
    exact KOne.map_id
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := (KOneN.ofMul (J := J)).surjective x
  exact congrArg (fun b => KOneN.ofMul (J := J) b) (DFunLike.congr_fun h a)

/-- `K₁` sends composites to composites. -/
theorem KOneN.map_comp (ψ : J' →⋆ₙₐ[ℂ] J'') (φ : J →⋆ₙₐ[ℂ] J') :
    KOneN.map (ψ.comp φ) = (KOneN.map ψ).comp (KOneN.map φ) := by
  have h : KOne.map (Unitization.starMap (ψ.comp φ)) =
      (KOne.map (Unitization.starMap ψ)).comp (KOne.map (Unitization.starMap φ)) := by
    rw [Unitization.starMap_comp]
    exact KOne.map_comp _ _
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := (KOneN.ofMul (J := J)).surjective x
  exact congrArg (fun b => KOneN.ofMul (J := J'') b) (DFunLike.congr_fun h a)

end KOne

end

end TWWSchafhauser
end Full
end GroupApproximation
