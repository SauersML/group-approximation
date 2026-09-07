import GroupApproximation.CharClass.LIXHsqEta
import GroupApproximation.CharClass.LIXPhiSquare
import GroupApproximation.CharClass.RelativeLineHomotopy
import GroupApproximation.CharClass.BundleFrame

/-!
# The far end of the comparison homotopy is a linear isomorphism

Lane `lix-hsq`.

The homotopy that compares `hsq`'s two routes contracts the chart-coordinate point to the
origin.  At the far end the base point is the section's zero and the fibre vector is the
chart's reading of the section pushed into the fibre there — and that composite is
**linear** in the chart coordinate, because `LIXHsqEta`'s reconstruction is.

This file writes that linear map down as `lixKLin`, proves it injective, and concludes that
it is a linear automorphism: the source and target are the same finite-dimensional real
vector space, so injectivity is surjectivity.  A linear automorphism is a homeomorphism of
the punctured pair, so its relative pullback is an isomorphism of the local model — and the
local model is a **line**, so that isomorphism is the identity.

## Where the injectivity comes from, and where it does not

Three steps, none of them a degree computation:

* `lixEtaLin` at the origin is injective, because `chartVec 0` starts with a `1` and the
  path's weight is `1` there (`LIXHsqEta`);
* the mapping torus at the section's zero, applied to a vector of `V`'s fibre placed in the
  second block, **returns that vector in its second block** — the circle height is `-1`
  there, so the coefficient `(1 - t)/2` is `1` (`mappingTorus_lixZero_mulVec`);
* the standard frame's adjoint is injective on the fibre, since `W Wᴴ` is the projection.

The nondegeneracy of the section's zero is not used here and is not reproved here.

## Main definitions

* `lixFrame` — the standard frame of the fibre at the section's zero.
* `lixKLin` — **the far end**, as an `ℝ`-linear map.
* `lixKHomeo` — the same, as a homeomorphism.

## Main results

* `lixFrame_mulVec_lixKLin` — the far end's fibre vector is the frame applied to `lixKLin`.
* `relPullback_lixKHomeo_eq_id` — **its relative pullback is the identity of the local
  model.**
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ} {G : baseM dd → Matrix (VIdx dd) (VIdx dd) ℂ}

/-! ## 1. The mapping torus at the section's zero -/

/-- Placing a vector of `V`'s fibre in the second block and applying the mapping torus at
the section's zero **returns the vector in the second block**: the circle height there is
`-1`, so the southern normal form's coefficient `(1 - t)/2` is `1`. -/
theorem mappingTorus_lixZero_mulVec (w : VIdx dd → ℂ)
    (hw : Vmat (lixZero dd).2 *ᵥ w = w) :
    mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w
      = Sum.elim ((2⁻¹ : ℂ) •
          ((mtTrans (G (lixZero dd).2) (circHoriz (lixZero dd).1))ᴴ *ᵥ w)) w := by
  have h := mtSection_south_form' (V := Vmat) (G := G) (y := circHoriz) (t := circHeight)
    (η := fun _ => w) (p := lixZero dd) hw
  rw [h]
  congr 1
  show ((((1 - circHeight (lixZero dd).1) / 2 : ℝ)) : ℂ) • w = w
  rw [show circHeight (lixZero dd).1 = -1 from circHeight_southPole]
  norm_num

/-- The second block of that value **is** the vector, so the assignment is injective on the
fibre of `V`. -/
theorem injective_mappingTorus_lixZero_mulVec {w w' : VIdx dd → ℂ}
    (hw : Vmat (lixZero dd).2 *ᵥ w = w) (hw' : Vmat (lixZero dd).2 *ᵥ w' = w')
    (h : mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w
      = mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w') :
    w = w' := by
  rw [mappingTorus_lixZero_mulVec (G := G) w hw,
    mappingTorus_lixZero_mulVec (G := G) w' hw'] at h
  funext i
  have := congrFun h (Sum.inr i)
  simpa using this

/-! ## 2. The standard frame at the section's zero -/

/-- The standard frame of the fibre of the mapping torus at the section's zero.  It is the
same frame `cc-bundle`'s trivialisation uses, since `stdFrame` depends on its two
hypotheses only through proof irrelevance. -/
def lixFrame (_hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Matrix (VIdx dd ⊕ VIdx dd) (Fin (lixRank dd)) ℂ :=
  stdFrame (isStarProjection_mappingTorus_lix hGu (lixZero dd)) (lixRank dd)
    (trace_mappingTorus_lixZero hGu)

theorem lixFrame_conjTranspose_mul (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (lixFrame hGc hGu)ᴴ * lixFrame hGc hGu = 1 :=
  stdFrame_conjTranspose_mul _ _ _

theorem lixFrame_mul_conjTranspose (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    lixFrame hGc hGu * (lixFrame hGc hGu)ᴴ
      = mappingTorus Vmat G circHoriz circHeight (lixZero dd) :=
  stdFrame_mul_conjTranspose _ _ _

/-- **The frame's adjoint is injective on the fibre.**  `W Wᴴ` is the projection, so `Wᴴ`
is recovered by applying `W`. -/
theorem injective_lixFrame_conjTranspose (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) {u u' : VIdx dd ⊕ VIdx dd → ℂ}
    (hu : mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ u = u)
    (hu' : mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ u' = u')
    (h : (lixFrame hGc hGu)ᴴ *ᵥ u = (lixFrame hGc hGu)ᴴ *ᵥ u') : u = u' := by
  have hback : ∀ y : VIdx dd ⊕ VIdx dd → ℂ,
      mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ y
        = lixFrame hGc hGu *ᵥ ((lixFrame hGc hGu)ᴴ *ᵥ y) := by
    intro y
    rw [Matrix.mulVec_mulVec, lixFrame_mul_conjTranspose hGc hGu]
  rw [← hu, ← hu', hback u, hback u', h]

/-! ## 3. The reconstruction at the origin, as a linear map -/

/-- `lixEtaLin` at the origin of the chart, bundled as a `ℂ`-linear map. -/
def lixEtaZeroMap (dd : Fin ℓ → ℕ) :
    ((Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) →ₗ[ℂ] (VIdx dd → ℂ) where
  toFun := lixEtaLin (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
  map_add' a b := by
    funext i
    cases i with
    | inl k => simp [lixEtaLin_inl]
    | inr h => simp only [lixEtaLin_inr, Prod.snd_add, Pi.add_apply]; ring
  map_smul' c a := by
    funext i
    cases i with
    | inl k => simp [lixEtaLin_inl]
    | inr h => simp only [lixEtaLin_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]; ring

theorem lixEtaZeroMap_apply (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    lixEtaZeroMap dd ab = lixEtaLin (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ab := rfl

theorem zero_circCoord_mem : ((0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ))).1.2
    ∈ Ioo (-1 : ℝ) 1 := by
  constructor <;> norm_num

theorem injective_lixEtaZeroMap (dd : Fin ℓ → ℕ) :
    Function.Injective (lixEtaZeroMap dd) := by
  refine (injective_iff_map_eq_zero (lixEtaZeroMap dd)).mpr fun ab hab => ?_
  exact (lixEtaLin_eq_zero_iff zero_circCoord_mem ab).mp hab

/-- The reconstruction at the origin lands in the fibre of `V` at the section's zero. -/
theorem Vmat_lixZero_mulVec_lixEtaZeroMap
    (ab : (Fin 3 → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    Vmat (lixZero dd).2 *ᵥ (lixEtaZeroMap dd ab) = lixEtaZeroMap dd ab := by
  have h := Vmat_mulVec_lixEtaLin (0 : ChartSrc × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ab
  rwa [lixBaseChartFun_zero] at h

/-! ## 4. The far end -/

/-- The second block of the mapping torus at the section's zero, which is what placing a
vector in the second block and applying the torus amounts to. -/
theorem submatrix_inr_mulVec
    (M : Matrix (VIdx dd ⊕ VIdx dd) (VIdx dd ⊕ VIdx dd) ℂ) (w : VIdx dd → ℂ) :
    M.submatrix id Sum.inr *ᵥ w = M *ᵥ Sum.elim 0 w := by
  funext i
  show ∑ j, M i (Sum.inr j) * w j
    = ∑ c, M i c * (Sum.elim (0 : VIdx dd → ℂ) w) c
  rw [Fintype.sum_sum_type
    (f := fun c : VIdx dd ⊕ VIdx dd => M i c * (Sum.elim (0 : VIdx dd → ℂ) w) c)]
  simp

/-- The matrix of the far end. -/
def lixKMat (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Matrix (Fin (lixRank dd)) (VIdx dd) ℂ :=
  (lixFrame hGc hGu)ᴴ *
    ((mappingTorus Vmat G circHoriz circHeight (lixZero dd)).submatrix id Sum.inr)

theorem lixKMat_mulVec (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (w : VIdx dd → ℂ) :
    lixKMat hGc hGu *ᵥ w
      = (lixFrame hGc hGu)ᴴ *ᵥ
        (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w) := by
  rw [lixKMat, ← Matrix.mulVec_mulVec, submatrix_inr_mulVec]

/-- **The far end of the comparison homotopy, as an `ℝ`-linear map.** -/
def lixKLin (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (Fin (lixRank dd) → ℂ) →ₗ[ℝ] (Fin (lixRank dd) → ℂ) :=
  (((Matrix.mulVecLin (lixKMat hGc hGu)).restrictScalars ℝ).comp
      ((lixEtaZeroMap dd).restrictScalars ℝ)).comp
    ((lixCoordEquiv dd).symm.toLinearEquiv.toLinearMap)

theorem lixKLin_apply (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m))
    (v : Fin (lixRank dd) → ℂ) :
    lixKLin hGc hGu v
      = lixKMat hGc hGu *ᵥ (lixEtaZeroMap dd ((lixCoordEquiv dd).symm v)) := rfl

/-- **The far end's fibre vector is the frame applied to `lixKLin`.**  The vector lies in
the fibre, and `W Wᴴ` is the projection there. -/
theorem lixFrame_mulVec_lixKLin (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (v : Fin (lixRank dd) → ℂ) :
    lixFrame hGc hGu *ᵥ lixKLin hGc hGu v
      = mappingTorus Vmat G circHoriz circHeight (lixZero dd)
        *ᵥ Sum.elim 0 (lixEtaZeroMap dd ((lixCoordEquiv dd).symm v)) := by
  rw [lixKLin_apply, lixKMat_mulVec, Matrix.mulVec_mulVec, lixFrame_mul_conjTranspose,
    Matrix.mulVec_mulVec]
  congr 1
  exact ((isStarProjection_mappingTorus_lix hGu (lixZero dd)).isIdempotentElem.eq)

/-! ## 5. It is an automorphism -/

theorem injective_lixKLin (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Function.Injective (lixKLin (dd := dd) hGc hGu) := by
  intro v v' hvv
  set w := lixEtaZeroMap dd ((lixCoordEquiv dd).symm v) with hwdef
  set w' := lixEtaZeroMap dd ((lixCoordEquiv dd).symm v') with hw'def
  have hfib : ∀ y : VIdx dd → ℂ, Vmat (lixZero dd).2 *ᵥ y = y →
      mappingTorus Vmat G circHoriz circHeight (lixZero dd)
          *ᵥ (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 y)
        = mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 y := by
    intro y _
    rw [Matrix.mulVec_mulVec,
      (isStarProjection_mappingTorus_lix hGu (lixZero dd)).isIdempotentElem.eq]
  have hw : Vmat (lixZero dd).2 *ᵥ w = w := Vmat_lixZero_mulVec_lixEtaZeroMap _
  have hw' : Vmat (lixZero dd).2 *ᵥ w' = w' := Vmat_lixZero_mulVec_lixEtaZeroMap _
  have hK : (lixFrame hGc hGu)ᴴ *ᵥ
        (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w)
      = (lixFrame hGc hGu)ᴴ *ᵥ
        (mappingTorus Vmat G circHoriz circHeight (lixZero dd) *ᵥ Sum.elim 0 w') := by
    rw [← lixKMat_mulVec, ← lixKMat_mulVec]
    exact hvv
  have hu := injective_lixFrame_conjTranspose hGc hGu (hfib w hw) (hfib w' hw') hK
  have hww : w = w' := injective_mappingTorus_lixZero_mulVec (G := G) hw hw' hu
  have hab : (lixCoordEquiv dd).symm v = (lixCoordEquiv dd).symm v' :=
    injective_lixEtaZeroMap dd hww
  exact (lixCoordEquiv dd).symm.injective hab

theorem bijective_lixKLin (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    Function.Bijective (lixKLin (dd := dd) hGc hGu) :=
  ⟨injective_lixKLin hGc hGu,
    (LinearMap.injective_iff_surjective (f := lixKLin (dd := dd) hGc hGu)).mp
      (injective_lixKLin hGc hGu)⟩

/-- **The far end, as a linear automorphism.** -/
def lixKEquiv (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (Fin (lixRank dd) → ℂ) ≃ₗ[ℝ] (Fin (lixRank dd) → ℂ) :=
  LinearEquiv.ofBijective (lixKLin hGc hGu) (bijective_lixKLin hGc hGu)

/-- **The far end, as a homeomorphism.** -/
def lixKHomeo (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    (Fin (lixRank dd) → ℂ) ≃ₜ (Fin (lixRank dd) → ℂ) :=
  (lixKEquiv hGc hGu).toContinuousLinearEquiv.toHomeomorph

/-- The far end, as an isomorphism of spaces. -/
def lixKIso (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of (Fin (lixRank dd) → ℂ) ≅ TopCat.of (Fin (lixRank dd) → ℂ) :=
  TopCat.isoOfHomeo (lixKHomeo hGc hGu)

/-- The far end, as a morphism of spaces. -/
def lixKMap (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    TopCat.of (Fin (lixRank dd) → ℂ) ⟶ TopCat.of (Fin (lixRank dd) → ℂ) :=
  (lixKIso hGc hGu).hom

@[simp] theorem lixKHomeo_apply (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) (v : Fin (lixRank dd) → ℂ) :
    lixKHomeo hGc hGu v = lixKLin hGc hGu v := rfl

/-! ## 6. Its relative pullback is the identity -/

theorem lixKHomeo_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ puncturedSet (lixRank dd),
      (ConcreteCategory.hom (lixKMap hGc hGu)) x
        ∈ puncturedSet (lixRank dd) := by
  intro x hx hcon
  refine hx ?_
  have : lixKLin hGc hGu x = lixKLin hGc hGu 0 := by
    rw [map_zero]
    exact hcon
  exact injective_lixKLin hGc hGu this

theorem lixKHomeo_symm_mapsTo (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    ∀ x ∈ puncturedSet (lixRank dd),
      (ConcreteCategory.hom (lixKIso hGc hGu).inv) x
        ∈ puncturedSet (lixRank dd) := by
  intro x hx hcon
  refine hx ?_
  have h : (lixKHomeo hGc hGu).symm x = (lixKHomeo hGc hGu).symm 0 := by
    rw [show ((lixKHomeo hGc hGu).symm 0 : Fin (lixRank dd) → ℂ) = 0 from
      (lixKEquiv hGc hGu).symm.map_zero]
    exact hcon
  have := (lixKHomeo hGc hGu).symm.injective h
  simpa using this

/-- **The far end's relative pullback is the identity of the local model.**  It is an
isomorphism because a linear automorphism is a homeomorphism of the punctured pair, and it
is the identity because the local model is a line. -/
theorem relPullback_lixKHomeo_eq_id (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)) :
    relPullback (ZMod 2) (lixKMap hGc hGu) (lixKHomeo_mapsTo hGc hGu) (2 * lixRank dd)
      = 𝟙 (relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
        (puncturedSet (lixRank dd)) (2 * lixRank dd)) := by
  refine RelativeSupport.relPullback_eq_id_of_line _ _ _ (localEquiv (lixRank dd)) ?_
  intro a b hab
  have key : ∀ x : ↥(relCohomology (ZMod 2) (TopCat.of (Fin (lixRank dd) → ℂ))
      (puncturedSet (lixRank dd)) (2 * lixRank dd)),
      (relPairIso (ZMod 2) (lixKIso hGc hGu) (lixKHomeo_mapsTo hGc hGu)
        (lixKHomeo_symm_mapsTo hGc hGu) (2 * lixRank dd)).inv.hom
        ((relPullback (ZMod 2) (lixKMap hGc hGu) (lixKHomeo_mapsTo hGc hGu)
          (2 * lixRank dd)).hom x) = x :=
    fun x => iso_inv_hom_apply (relPairIso (ZMod 2) (lixKIso hGc hGu)
      (lixKHomeo_mapsTo hGc hGu) (lixKHomeo_symm_mapsTo hGc hGu) (2 * lixRank dd)) x
  rw [← key a, ← key b, hab]

/-! Printed on every build. -/

#print axioms relPullback_lixKHomeo_eq_id

end GroupApproximation.CharClass
