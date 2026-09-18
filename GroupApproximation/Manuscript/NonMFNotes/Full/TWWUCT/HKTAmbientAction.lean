import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAffineMap

/-!
# The action of an affine isometric action on the ambient algebra `ℝ × H →ᵇ C`

Lane TWWUCT-C (WO-TWWUCT-C).  An affine isometric action `g • h = π_g h + b_g` acts on the ambient
C⋆-algebra of bounded continuous functions by

`(α_g F)(t, h) = orth(π_g) (F (t, g⁻¹ • h))`

(HKT 1998, §4; HK 2001, §3: the induced action on `A(H)`).  It carries the stage-`E` generators
to the stage-`g • E` generators:

* `α_g (evenGen E k) = evenGen (g • E) (orth π_g ∘ k ∘ π_g⁻¹)`, and likewise for the odd
  generators.

This file provides:

* `AffineIsometricAction.ambientMap`: the map `α_g`, with `ambientMap_mul` and `ambientMap_one`.
* `AffineIsometricAction.ambientAct C g`: `α_g` bundled as a ⋆-algebra automorphism.
* `ambientAct_evenGen`, `ambientAct_oddGen`: the generators are transported.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

open Filter Topology

namespace CliffordSystem

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- `orth_clifford` in the form `orth U (c(t, h)) = c(t, U h)`. -/
theorem orth_clifford_pair (U : H ≃ₗᵢ[ℝ] H) (t : ℝ) (h : H) :
    orth (C := C) U (clifford (t, h)) = clifford (t, U h) :=
  orth_clifford U (t, h)

end CliffordSystem

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

theorem linearPart_one_eq : b.linearPart 1 = 1 :=
  LinearIsometryEquiv.ext fun ξ => b.linearPart_one ξ

theorem linearPart_mul_eq (g h : G) : b.linearPart (g * h) = b.linearPart g * b.linearPart h :=
  LinearIsometryEquiv.ext fun ξ => b.linearPart_mul g h ξ

theorem continuous_twist (g : G) : Continuous fun x : ℝ × H => (x.1, b.act g⁻¹ x.2) :=
  continuous_fst.prodMk ((b.continuous_act g⁻¹).comp continuous_snd)

/-- The ambient action `(α_g F)(t, h) = orth(π_g) (F (t, g⁻¹ • h))`. -/
def ambientMap (g : G) (F : ℝ × H →ᵇ C) : ℝ × H →ᵇ C :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ × H => CliffordSystem.orth (C := C) (b.linearPart g) (F (x.1, b.act g⁻¹ x.2)))
    ((StarAlgEquiv.isometry (CliffordSystem.orth (C := C) (b.linearPart g))).continuous.comp
      (F.continuous.comp (b.continuous_twist g))) ‖F‖
    (fun x => by
      show ‖CliffordSystem.orth (C := C) (b.linearPart g) (F (x.1, b.act g⁻¹ x.2))‖ ≤ ‖F‖
      rw [StarAlgEquiv.norm_map]
      exact F.norm_coe_le_norm _)

theorem ambientMap_apply (g : G) (F : ℝ × H →ᵇ C) (t : ℝ) (y : H) :
    b.ambientMap g F (t, y) =
      CliffordSystem.orth (C := C) (b.linearPart g) (F (t, b.act g⁻¹ y)) :=
  rfl

theorem ambientMap_mul (g h : G) (F : ℝ × H →ᵇ C) :
    b.ambientMap (g * h) F = b.ambientMap g (b.ambientMap h F) := by
  ext ⟨t, y⟩
  rw [ambientMap_apply, ambientMap_apply, ambientMap_apply, mul_inv_rev, b.act_mul,
    b.linearPart_mul_eq, CliffordSystem.orth_mul]

theorem ambientMap_one (F : ℝ × H →ᵇ C) : b.ambientMap 1 F = F := by
  ext ⟨t, y⟩
  rw [ambientMap_apply, inv_one, b.act_one, b.linearPart_one_eq, CliffordSystem.orth_one]

variable (C) in
/-- The ambient action `α_g` as a ⋆-algebra automorphism of `ℝ × H →ᵇ C`. -/
def ambientAct (g : G) : (ℝ × H →ᵇ C) ≃⋆ₐ[ℂ] (ℝ × H →ᵇ C) where
  toFun := b.ambientMap g
  invFun := b.ambientMap g⁻¹
  left_inv F := by
    show b.ambientMap g⁻¹ (b.ambientMap g F) = F
    rw [← b.ambientMap_mul, inv_mul_cancel, b.ambientMap_one]
  right_inv F := by
    show b.ambientMap g (b.ambientMap g⁻¹ F) = F
    rw [← b.ambientMap_mul, mul_inv_cancel, b.ambientMap_one]
  map_mul' F F' := by
    ext ⟨t, y⟩
    exact map_mul (CliffordSystem.orth (C := C) (b.linearPart g)) (F (t, b.act g⁻¹ y))
      (F' (t, b.act g⁻¹ y))
  map_add' F F' := by
    ext ⟨t, y⟩
    exact map_add (CliffordSystem.orth (C := C) (b.linearPart g)) (F (t, b.act g⁻¹ y))
      (F' (t, b.act g⁻¹ y))
  map_star' F := by
    ext ⟨t, y⟩
    exact map_star (CliffordSystem.orth (C := C) (b.linearPart g)) (F (t, b.act g⁻¹ y))
  map_smul' c F := by
    ext ⟨t, y⟩
    exact map_smul (CliffordSystem.orth (C := C) (b.linearPart g)) c (F (t, b.act g⁻¹ y))

theorem ambientAct_apply (g : G) (F : ℝ × H →ᵇ C) : b.ambientAct C g F = b.ambientMap g F :=
  rfl

theorem ambientAct_one : b.ambientAct C 1 = 1 :=
  StarAlgEquiv.ext fun F => b.ambientMap_one F

theorem ambientAct_mul (g h : G) : b.ambientAct C (g * h) = b.ambientAct C g * b.ambientAct C h :=
  StarAlgEquiv.ext fun F => b.ambientMap_mul g h F

/-- `α_g` carries the even generator of `E` with coefficient `k` to the even generator of `g • E`
with coefficient `orth π_g ∘ k ∘ π_g⁻¹`. -/
theorem ambientMap_evenGen (g : G) (E : FinDimAffine H) (k : E.dir →ᵇ C) :
    b.ambientMap g (E.evenGen k) =
      (E.mapAffine (b.linearPart g) (b.cocycle g)).evenGen
        (E.transportCoeff (b.linearPart g) (b.cocycle g) k) := by
  ext ⟨t, y⟩
  obtain ⟨y', rfl⟩ : ∃ y' : H, y = b.act g y' := ⟨b.act g⁻¹ y, (b.act_act_inv g y).symm⟩
  rw [ambientMap_apply, b.act_inv_act, FinDimAffine.evenGen_apply, FinDimAffine.evenGen_apply]
  dsimp only
  rw [b.act_apply, FinDimAffine.gaussian_mapAffine, FinDimAffine.transportCoeff_foot,
    map_smul (CliffordSystem.orth (C := C) (b.linearPart g))]

/-- `α_g` carries the odd generator of `E` with coefficient `k` to the odd generator of `g • E`
with coefficient `orth π_g ∘ k ∘ π_g⁻¹`. -/
theorem ambientMap_oddGen (g : G) (E : FinDimAffine H) (k : E.dir →ᵇ C) :
    b.ambientMap g (E.oddGen k) =
      (E.mapAffine (b.linearPart g) (b.cocycle g)).oddGen
        (E.transportCoeff (b.linearPart g) (b.cocycle g) k) := by
  ext ⟨t, y⟩
  obtain ⟨y', rfl⟩ : ∃ y' : H, y = b.act g y' := ⟨b.act g⁻¹ y, (b.act_act_inv g y).symm⟩
  rw [ambientMap_apply, b.act_inv_act, FinDimAffine.oddGen_apply, FinDimAffine.oddGen_apply]
  dsimp only
  rw [b.act_apply, FinDimAffine.gaussian_mapAffine, FinDimAffine.perp_mapAffine,
    FinDimAffine.transportCoeff_foot, map_smul (CliffordSystem.orth (C := C) (b.linearPart g)),
    map_mul (CliffordSystem.orth (C := C) (b.linearPart g)), CliffordSystem.orth_clifford_pair]

/-- `α_g` maps stage-`E` generators to stage-`g • E` generators. -/
theorem ambientMap_mem_stageGenerators (g : G) {E : FinDimAffine H} {F : ℝ × H →ᵇ C}
    (hF : F ∈ E.stageGenerators C) :
    b.ambientMap g F ∈ (E.mapAffine (b.linearPart g) (b.cocycle g)).stageGenerators C := by
  obtain ⟨k, hk, rfl | rfl⟩ := hF
  · rw [b.ambientMap_evenGen g E k]
    exact FinDimAffine.evenGen_mem_stageGenerators _ (E.isStageCoeff_transport _ _ hk)
  · rw [b.ambientMap_oddGen g E k]
    exact FinDimAffine.oddGen_mem_stageGenerators _ (E.isStageCoeff_transport _ _ hk)

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT
