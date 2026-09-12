import GroupApproximation.CharClass.LIXKGenLocalEta
import GroupApproximation.CharClass.LIXHsqLinear
import GroupApproximation.Meta.AxiomGuard

/-!
# The far end of the comparison homotopy at the `i`-th zero is a linear isomorphism, at rank `n`

Lane `lix-oddside` (lead ruling 2026-09-11: leaf (3) of the `k`-zero Step C data, the rank-`n`
port of `CharClass/LIXHsqLinear.lean` at the `i`-th zero).

At the far end of the comparison homotopy the base point is the `i`-th zero and the fibre vector
is the chart's reading of the section pushed into the fibre there.  That composite is linear in
the chart coordinate (`LIXKGenLocalEta`), injective, hence a linear automorphism of `ℂ^r`, and
its relative pullback on the local model is the identity because the local model is a line.

The names carry `KG` (`lixKGFrame`, `lixKGLin`, …) so that they never share a spelling with the
rank-two far end `lixKLin`, `lixKHomeo`, … of `CharClass/LIXHsqLinear.lean`.

## Main definitions

* `lixKGFrame` — the standard frame of the fibre at the `i`-th zero.
* `lixKGLin` — **the far end**, as an `ℝ`-linear map; `lixKGHomeo`, `lixKGMap`.

## Main results

* `lixKGFrame_mulVec_lixKGLin` — the far end's fibre vector is the frame applied to `lixKGLin`.
* `relPullback_lixKGHomeo_eq_id` — its relative pullback is the identity of the local model.
-/

noncomputable section

namespace GroupApproximation.CharClass

namespace KGen

open scoped Matrix
open Set CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The mapping torus at the `i`-th zero -/

theorem trace_mappingTorus_lixKZero (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Matrix.trace (mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i))
      = ((lixRank n dd : ℕ) : ℂ) := by
  rw [trace_mappingTorus]
  exact Gen.trace_Vmat n (lixKZero n k dd i).2

/-- Placing a vector of `V`'s fibre in the second block and applying the mapping torus at the
`i`-th zero returns the vector in the second block. -/
theorem mappingTorus_lixKZero_mulVec (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (w : Gen.VIdx n dd → ℂ) (hw : Gen.Vmat n (lixKZero n k dd i).2 *ᵥ w = w) :
    mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ Sum.elim 0 w
      = Sum.elim ((2⁻¹ : ℂ) •
          ((mtTrans (G (lixKZero n k dd i).2) (circHoriz (lixKZero n k dd i).1))ᴴ *ᵥ w)) w := by
  have h := mtSection_south_form' (V := Gen.Vmat n) (G := G) (y := circHoriz) (t := circHeight)
    (η := fun _ => w) (p := lixKZero n k dd i) hw
  rw [h]
  congr 1
  show ((((1 - circHeight (lixKZero n k dd i).1) / 2 : ℝ)) : ℂ) • w = w
  rw [show circHeight (lixKZero n k dd i).1 = -1 from circHeight_southPole]
  norm_num

theorem injective_mappingTorus_lixKZero_mulVec (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    {w w' : Gen.VIdx n dd → ℂ}
    (hw : Gen.Vmat n (lixKZero n k dd i).2 *ᵥ w = w)
    (hw' : Gen.Vmat n (lixKZero n k dd i).2 *ᵥ w' = w')
    (h : mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ Sum.elim 0 w
      = mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ Sum.elim 0 w') :
    w = w' := by
  rw [mappingTorus_lixKZero_mulVec n k i (G := G) w hw,
    mappingTorus_lixKZero_mulVec n k i (G := G) w' hw'] at h
  funext x
  have := congrFun h (Sum.inr x)
  simpa using this

/-! ## 2. The standard frame at the `i`-th zero -/

/-- The standard frame of the fibre of the mapping torus at the `i`-th zero. -/
def lixKGFrame (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (_hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Matrix (Gen.VIdx n dd ⊕ Gen.VIdx n dd) (Fin (lixRank n dd)) ℂ :=
  stdFrame (isStarProjection_mappingTorus_lix n hGu (lixKZero n k dd i)) (lixRank n dd)
    (trace_mappingTorus_lixKZero n k i hGu)

theorem lixKGFrame_conjTranspose_mul (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (lixKGFrame n k i hGc hGu)ᴴ * lixKGFrame n k i hGc hGu = 1 :=
  stdFrame_conjTranspose_mul _ _ _

theorem lixKGFrame_mul_conjTranspose (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    lixKGFrame n k i hGc hGu * (lixKGFrame n k i hGc hGu)ᴴ
      = mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) :=
  stdFrame_mul_conjTranspose _ _ _

theorem injective_lixKGFrame_conjTranspose (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    {u u' : Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ}
    (hu : mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ u = u)
    (hu' : mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ u' = u')
    (h : (lixKGFrame n k i hGc hGu)ᴴ *ᵥ u = (lixKGFrame n k i hGc hGu)ᴴ *ᵥ u') : u = u' := by
  have hback : ∀ y : Gen.VIdx n dd ⊕ Gen.VIdx n dd → ℂ,
      mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ y
        = lixKGFrame n k i hGc hGu *ᵥ ((lixKGFrame n k i hGc hGu)ᴴ *ᵥ y) := by
    intro y
    rw [Matrix.mulVec_mulVec, lixKGFrame_mul_conjTranspose n k i hGc hGu]
  rw [← hu, ← hu', hback u, hback u', h]

/-! ## 3. The reconstruction at the origin, as a linear map -/

/-- `lixKEtaLin` at the origin of the chart, bundled as a `ℂ`-linear map. -/
def lixKGEtaZeroMap (n : ℕ) (dd : Fin ℓ → ℕ) :
    ((Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) →ₗ[ℂ] (Gen.VIdx n dd → ℂ) where
  toFun := lixKEtaLin n ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ))
  map_add' a b := by
    funext x
    cases x with
    | inl a' => simp [lixKEtaLin_inl]
    | inr h => simp only [lixKEtaLin_inr, Prod.snd_add, Pi.add_apply]; ring
  map_smul' c a := by
    funext x
    cases x with
    | inl a' => simp [lixKEtaLin_inl]
    | inr h => simp only [lixKEtaLin_inr, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]; ring

theorem lixKGEtaZeroMap_apply (n : ℕ) (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    lixKGEtaZeroMap n dd ab
      = lixKEtaLin n ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ab := rfl

theorem zero_circCoord_memK (n : ℕ) :
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)).1.2 ∈ Ioo (-1 : ℝ) 1 := by
  show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1
  constructor <;> norm_num

theorem injective_lixKGEtaZeroMap (n : ℕ) (dd : Fin ℓ → ℕ) :
    Function.Injective (lixKGEtaZeroMap n dd) := by
  refine (injective_iff_map_eq_zero (lixKGEtaZeroMap n dd)).mpr fun ab hab => ?_
  exact (lixKEtaLin_eq_zero_iff n (zero_circCoord_memK (dd := dd) n) ab).mp hab

/-- The reconstruction at the origin lands in the fibre of `V` at the `i`-th zero. -/
theorem Vmat_lixKZero_mulVec_lixKGEtaZeroMap (n k : ℕ) (i : Fin (k + 1))
    (ab : (Fin (n + 1) → ℂ) × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) :
    Gen.Vmat n (lixKZero n k dd i).2 *ᵥ (lixKGEtaZeroMap n dd ab) = lixKGEtaZeroMap n dd ab := by
  have h := Vmat_mulVec_lixKEtaLin n k i
    ((0, 0) : ChartSrc n × (∀ j : Fin ℓ, Fin (dd j) → ℂ)) ab
  rwa [lixKBaseChart_zero n k dd i] at h

/-! ## 4. The far end -/

theorem submatrix_inr_mulVecG {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ) (w : ι → ℂ) :
    M.submatrix id Sum.inr *ᵥ w = M *ᵥ Sum.elim 0 w := by
  funext x
  show ∑ j, M x (Sum.inr j) * w j
    = ∑ c, M x c * (Sum.elim (0 : ι → ℂ) w) c
  rw [Fintype.sum_sum_type
    (f := fun c : ι ⊕ ι => M x c * (Sum.elim (0 : ι → ℂ) w) c)]
  simp

/-- The matrix of the far end at the `i`-th zero. -/
def lixKGMat (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Matrix (Fin (lixRank n dd)) (Gen.VIdx n dd) ℂ :=
  (lixKGFrame n k i hGc hGu)ᴴ *
    ((mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)).submatrix id Sum.inr)

theorem lixKGMat_mulVec (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (w : Gen.VIdx n dd → ℂ) :
    lixKGMat n k i hGc hGu *ᵥ w
      = (lixKGFrame n k i hGc hGu)ᴴ *ᵥ
        (mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ Sum.elim 0 w) := by
  rw [lixKGMat, ← Matrix.mulVec_mulVec, submatrix_inr_mulVecG]

/-- **The far end of the comparison homotopy at the `i`-th zero, as an `ℝ`-linear map.** -/
def lixKGLin (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (Fin (lixRank n dd) → ℂ) →ₗ[ℝ] (Fin (lixRank n dd) → ℂ) :=
  (((Matrix.mulVecLin (lixKGMat n k i hGc hGu)).restrictScalars ℝ).comp
      ((lixKGEtaZeroMap n dd).restrictScalars ℝ)).comp
    ((lixKCoordEquiv n dd).symm.toLinearEquiv.toLinearMap)

theorem lixKGLin_apply (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : Fin (lixRank n dd) → ℂ) :
    lixKGLin n k i hGc hGu v
      = lixKGMat n k i hGc hGu *ᵥ (lixKGEtaZeroMap n dd ((lixKCoordEquiv n dd).symm v)) := rfl

/-- **The far end's fibre vector is the frame applied to `lixKGLin`.** -/
theorem lixKGFrame_mulVec_lixKGLin (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : Fin (lixRank n dd) → ℂ) :
    lixKGFrame n k i hGc hGu *ᵥ lixKGLin n k i hGc hGu v
      = mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
        *ᵥ Sum.elim 0 (lixKGEtaZeroMap n dd ((lixKCoordEquiv n dd).symm v)) := by
  rw [lixKGLin_apply, lixKGMat_mulVec, Matrix.mulVec_mulVec, lixKGFrame_mul_conjTranspose,
    Matrix.mulVec_mulVec]
  congr 1
  exact ((isStarProjection_mappingTorus_lix n hGu (lixKZero n k dd i)).isIdempotentElem.eq)

/-! ## 5. It is an automorphism -/

theorem injective_lixKGLin (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Function.Injective (lixKGLin n k i hGc hGu) := by
  intro v v' hvv
  set w := lixKGEtaZeroMap n dd ((lixKCoordEquiv n dd).symm v) with hwdef
  set w' := lixKGEtaZeroMap n dd ((lixKCoordEquiv n dd).symm v') with hw'def
  have hfib : ∀ y : Gen.VIdx n dd → ℂ, Gen.Vmat n (lixKZero n k dd i).2 *ᵥ y = y →
      mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
          *ᵥ (mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
            *ᵥ Sum.elim 0 y)
        = mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
            *ᵥ Sum.elim 0 y := by
    intro y _
    rw [Matrix.mulVec_mulVec,
      (isStarProjection_mappingTorus_lix n hGu (lixKZero n k dd i)).isIdempotentElem.eq]
  have hw : Gen.Vmat n (lixKZero n k dd i).2 *ᵥ w = w :=
    Vmat_lixKZero_mulVec_lixKGEtaZeroMap n k i _
  have hw' : Gen.Vmat n (lixKZero n k dd i).2 *ᵥ w' = w' :=
    Vmat_lixKZero_mulVec_lixKGEtaZeroMap n k i _
  have hK : (lixKGFrame n k i hGc hGu)ᴴ *ᵥ
        (mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i) *ᵥ Sum.elim 0 w)
      = (lixKGFrame n k i hGc hGu)ᴴ *ᵥ
        (mappingTorus (Gen.Vmat n) G circHoriz circHeight (lixKZero n k dd i)
          *ᵥ Sum.elim 0 w') := by
    rw [← lixKGMat_mulVec, ← lixKGMat_mulVec]
    exact hvv
  have hu := injective_lixKGFrame_conjTranspose n k i hGc hGu (hfib w hw) (hfib w' hw') hK
  have hww : w = w' := injective_mappingTorus_lixKZero_mulVec n k i (G := G) hw hw' hu
  have hab : (lixKCoordEquiv n dd).symm v = (lixKCoordEquiv n dd).symm v' :=
    injective_lixKGEtaZeroMap n dd hww
  exact (lixKCoordEquiv n dd).symm.injective hab

theorem bijective_lixKGLin (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    Function.Bijective (lixKGLin n k i hGc hGu) :=
  ⟨injective_lixKGLin n k i hGc hGu,
    (LinearMap.injective_iff_surjective (f := lixKGLin n k i hGc hGu)).mp
      (injective_lixKGLin n k i hGc hGu)⟩

/-- **The far end, as a linear automorphism.** -/
def lixKGEquiv (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (Fin (lixRank n dd) → ℂ) ≃ₗ[ℝ] (Fin (lixRank n dd) → ℂ) :=
  LinearEquiv.ofBijective (lixKGLin n k i hGc hGu) (bijective_lixKGLin n k i hGc hGu)

/-- **The far end, as a homeomorphism.** -/
def lixKGHomeo (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    (Fin (lixRank n dd) → ℂ) ≃ₜ (Fin (lixRank n dd) → ℂ) :=
  (lixKGEquiv n k i hGc hGu).toContinuousLinearEquiv.toHomeomorph

/-- The far end, as an isomorphism of spaces. -/
def lixKGIso (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of (Fin (lixRank n dd) → ℂ) ≅ TopCat.of (Fin (lixRank n dd) → ℂ) :=
  TopCat.isoOfHomeo (lixKGHomeo n k i hGc hGu)

/-- The far end, as a morphism of spaces. -/
def lixKGMap (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    TopCat.of (Fin (lixRank n dd) → ℂ) ⟶ TopCat.of (Fin (lixRank n dd) → ℂ) :=
  (lixKGIso n k i hGc hGu).hom

@[simp] theorem lixKGHomeo_apply (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m))
    (v : Fin (lixRank n dd) → ℂ) :
    lixKGHomeo n k i hGc hGu v = lixKGLin n k i hGc hGu v := rfl

/-! ## 6. Its relative pullback is the identity -/

theorem lixKGHomeo_mapsTo (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (lixKGMap n k i hGc hGu)) x ∈ puncturedSet (lixRank n dd) := by
  intro x hx hcon
  refine hx ?_
  have : lixKGLin n k i hGc hGu x = lixKGLin n k i hGc hGu 0 := by
    rw [map_zero]
    exact hcon
  exact injective_lixKGLin n k i hGc hGu this

theorem lixKGHomeo_symm_mapsTo (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    ∀ x ∈ puncturedSet (lixRank n dd),
      (ConcreteCategory.hom (lixKGIso n k i hGc hGu).inv) x ∈ puncturedSet (lixRank n dd) := by
  intro x hx hcon
  refine hx ?_
  have h : (lixKGHomeo n k i hGc hGu).symm x = (lixKGHomeo n k i hGc hGu).symm 0 := by
    rw [show ((lixKGHomeo n k i hGc hGu).symm 0 : Fin (lixRank n dd) → ℂ) = 0 from
      (lixKGEquiv n k i hGc hGu).symm.map_zero]
    exact hcon
  have := (lixKGHomeo n k i hGc hGu).symm.injective h
  simpa using this

/-- **The far end's relative pullback is the identity of the local model.** -/
theorem relPullback_lixKGHomeo_eq_id (n k : ℕ) (i : Fin (k + 1))
    {G : Gen.baseM n dd → Matrix (Gen.VIdx n dd) (Gen.VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Gen.Vmat n m) (G m)) :
    relPullback (ZMod 2) (lixKGMap n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
        (2 * lixRank n dd)
      = 𝟙 (relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
        (puncturedSet (lixRank n dd)) (2 * lixRank n dd)) := by
  refine RelativeSupport.relPullback_eq_id_of_line _ _ _ (localEquiv (lixRank n dd)) ?_
  intro a b hab
  have key : ∀ x : ↥(relCohomology (ZMod 2) (TopCat.of (Fin (lixRank n dd) → ℂ))
      (puncturedSet (lixRank n dd)) (2 * lixRank n dd)),
      (relPairIso (ZMod 2) (lixKGIso n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
        (lixKGHomeo_symm_mapsTo n k i hGc hGu) (2 * lixRank n dd)).inv.hom
        ((relPullback (ZMod 2) (lixKGMap n k i hGc hGu) (lixKGHomeo_mapsTo n k i hGc hGu)
          (2 * lixRank n dd)).hom x) = x :=
    fun x => iso_inv_hom_apply (relPairIso (ZMod 2) (lixKGIso n k i hGc hGu)
      (lixKGHomeo_mapsTo n k i hGc hGu) (lixKGHomeo_symm_mapsTo n k i hGc hGu)
      (2 * lixRank n dd)) x
  rw [← key a, ← key b, hab]

end KGen

/-! Audited on every build. -/

#audit_axioms KGen.lixKGFrame_mulVec_lixKGLin
#audit_axioms KGen.relPullback_lixKGHomeo_eq_id

end GroupApproximation.CharClass
