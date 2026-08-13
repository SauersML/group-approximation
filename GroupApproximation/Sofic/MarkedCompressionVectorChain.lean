import GroupApproximation.Sofic.AdjointMatrix
import GroupApproximation.Sofic.ProjectionRankFlip

/-!
# The finite marked-compression vector chain

This file isolates step 11 of the marked-compression non-MF argument as a
dimension-free finite-dimensional estimate.  Let `P` be the Kazhdan spectral
projection, let `T` be the adjoint action of the compressor, and put

`Q = T * P * Tᴴ`.

If a vector `ξ` is almost captured by `P`, then `T ξ` is equally well
captured by `Q`.  If the reverse leakage `(1 - P) * Q` is small and a unitary
`A` almost fixes the range of `P`, then `A` almost fixes `T ξ`.  The main
estimate is

`|A(Tξ) - Tξ|² ≤ (2δ² + 16ε²)|ξ|² + 16κ`,

where `δ` bounds `‖(A-1)P‖`, `ε` bounds `‖(1-P)Q‖`, and `κ` bounds
the squared mass of `(1-P)ξ`.  No constant depends on the coordinate type.

The final theorem applies this to row-vectorized matrices under
`conjDouble`: for unitary matrices `Uₐ,Uₜ,C`, it bounds the normalized
Hilbert--Schmidt displacement of

`D = Uₜ C Uₜᴴ`

under conjugation by `Uₐ`.  A companion estimate turns this displacement
into a bound for the marked commutator.
-/

namespace GroupApproximation
namespace MarkedCompressionVectorChain

open Matrix KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Squared Euclidean mass -/

/-- The unnormalized squared Euclidean mass of a finite vector. -/
noncomputable def vecMass (x : Y → ℂ) : ℝ :=
  ∑ i : Y, Complex.normSq (x i)

theorem vecMass_nonneg (x : Y → ℂ) : 0 ≤ vecMass x :=
  Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg (x i)

theorem vecMass_add_le (x y : Y → ℂ) :
    vecMass (x + y) ≤ 2 * vecMass x + 2 * vecMass y := by
  unfold vecMass
  have hpoint : ∀ i : Y, Complex.normSq (x i + y i) ≤
      2 * Complex.normSq (x i) + 2 * Complex.normSq (y i) := by
    intro i
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    nlinarith [sq_nonneg ((x i).re - (y i).re),
      sq_nonneg ((x i).im - (y i).im)]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ ↦ hpoint i

/-- Operator norm controls squared Euclidean mass, with no dimension factor. -/
theorem vecMass_mulVec_le (M : Matrix Y Y ℂ) (x : Y → ℂ) :
    vecMass (M *ᵥ x) ≤ ‖M‖ ^ 2 * vecMass x :=
  sum_normSq_mulVec_le_general M x

/-- A unitary matrix preserves squared Euclidean mass. -/
theorem vecMass_unitary_mulVec {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (x : Y → ℂ) :
    vecMass (U *ᵥ x) = vecMass x := by
  apply sum_normSq_mulVec_of_star_mul_self
  exact Unitary.star_mul_self_of_mem hU

/-! ## Exact transport of a captured vector -/

/-- If `Q = T P Tᴴ`, then the complementary part of `T ξ` is exactly the
transport by `T` of the complementary part of `ξ`. -/
theorem one_sub_conjugate_mulVec (P T : Matrix Y Y ℂ)
    (hT : T ∈ Matrix.unitaryGroup Y ℂ) (x : Y → ℂ) :
    (1 - T * P * Tᴴ) *ᵥ (T *ᵥ x) = T *ᵥ ((1 - P) *ᵥ x) := by
  have hTT : Tᴴ * T = 1 := Unitary.star_mul_self_of_mem hT
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc Tᴴ T,
    hTT, Matrix.one_mul, Matrix.mulVec_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec]

/-- Exact unitary transport preserves the capture error. -/
theorem vecMass_one_sub_conjugate (P T : Matrix Y Y ℂ)
    (hT : T ∈ Matrix.unitaryGroup Y ℂ) (x : Y → ℂ) :
    vecMass ((1 - T * P * Tᴴ) *ᵥ (T *ᵥ x)) =
      vecMass ((1 - P) *ᵥ x) := by
  rw [one_sub_conjugate_mulVec P T hT x,
    vecMass_unitary_mulVec hT]

/-! ## The dimension-free chain -/

/-- **Finite marked-compression vector chain.**

Let `P` be an orthogonal projection, `T` and `A` unitaries, and
`Q = T P Tᴴ`.  If

* `‖(A - 1)P‖ ≤ δ`, so `A` almost fixes the `P`-space;
* `‖(1 - P)Q‖ ≤ ε`, the reverse leakage supplied by equal-rank flip;
* `|(1-P)ξ|² ≤ κ`, so the lamp vector is captured by `P`;

then `A` almost fixes the transported vector `Tξ`, with an explicit bound
independent of `card Y`. -/
theorem transported_displacement_le
    (hY : 0 < Fintype.card Y)
    {P T A : Matrix Y Y ℂ} (hP : IsOrthogonalProjectionMatrix P)
    (hT : T ∈ Matrix.unitaryGroup Y ℂ)
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    {δ ε κ : ℝ}
    (hfix : ‖(A - 1) * P‖ ≤ δ)
    (hreverse : ‖(1 - P) * (T * P * Tᴴ)‖ ≤ ε)
    {x : Y → ℂ} (hcapture : vecMass ((1 - P) *ᵥ x) ≤ κ) :
    vecMass (A *ᵥ (T *ᵥ x) - T *ᵥ x) ≤
      (2 * δ ^ 2 + 16 * ε ^ 2) * vecMass x + 16 * κ := by
  letI : Nonempty Y := Fintype.card_pos_iff.mp hY
  let Q : Matrix Y Y ℂ := T * P * Tᴴ
  let y : Y → ℂ := T *ᵥ x
  have hyMass : vecMass y = vecMass x := vecMass_unitary_mulVec hT x
  have hQcapture : vecMass ((1 - Q) *ᵥ y) ≤ κ := by
    rw [Q, y, vecMass_one_sub_conjugate P T hT x]
    exact hcapture
  have hPcomp : IsOrthogonalProjectionMatrix (1 - P) :=
    one_sub_isOrthogonalProjection hP
  have hdecomp : (1 - P) *ᵥ y =
      ((1 - P) * Q) *ᵥ y + (1 - P) *ᵥ ((1 - Q) *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec]
    have : (1 - P) = (1 - P) * Q + (1 - P) * (1 - Q) := by
      noncomm_ring
    rw [this, Matrix.add_mulVec]
  have hreverse' : ‖(1 - P) * Q‖ ≤ ε := by simpa [Q] using hreverse
  have hcompMass : vecMass ((1 - P) *ᵥ y) ≤
      2 * ε ^ 2 * vecMass x + 2 * κ := by
    rw [hdecomp]
    calc
      vecMass (((1 - P) * Q) *ᵥ y + (1 - P) *ᵥ ((1 - Q) *ᵥ y)) ≤
          2 * vecMass (((1 - P) * Q) *ᵥ y) +
            2 * vecMass ((1 - P) *ᵥ ((1 - Q) *ᵥ y)) :=
        vecMass_add_le _ _
      _ ≤ 2 * (ε ^ 2 * vecMass y) +
          2 * vecMass ((1 - Q) *ᵥ y) := by
        gcongr
        · calc
            vecMass (((1 - P) * Q) *ᵥ y) ≤
                ‖(1 - P) * Q‖ ^ 2 * vecMass y := vecMass_mulVec_le _ _
            _ ≤ ε ^ 2 * vecMass y := by
              gcongr
              exact pow_le_pow_left (norm_nonneg _) hreverse' 2
        · exact sum_normSq_mulVec_proj_le hPcomp _
      _ ≤ 2 * ε ^ 2 * vecMass x + 2 * κ := by
        rw [hyMass]
        linarith
  have hAone : ‖A - 1‖ ≤ 2 := by
    have hAnorm : ‖A‖ = 1 := CStarRing.norm_of_mem_unitary hA
    calc
      ‖A - 1‖ ≤ ‖A‖ + ‖1‖ := norm_sub_le _ _
      _ = 2 := by rw [hAnorm, norm_one]; norm_num
  have hdisp : A *ᵥ y - y =
      ((A - 1) * P) *ᵥ y + (A - 1) *ᵥ ((1 - P) *ᵥ y) := by
    have hy : A *ᵥ y - y = (A - 1) *ᵥ y := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [hy]
    have hsplit : (A - 1) = (A - 1) * P + (A - 1) * (1 - P) := by
      noncomm_ring
    rw [hsplit, Matrix.add_mulVec, Matrix.mulVec_mulVec]
  rw [hdisp]
  calc
    vecMass (((A - 1) * P) *ᵥ y + (A - 1) *ᵥ ((1 - P) *ᵥ y)) ≤
        2 * vecMass (((A - 1) * P) *ᵥ y) +
          2 * vecMass ((A - 1) *ᵥ ((1 - P) *ᵥ y)) :=
      vecMass_add_le _ _
    _ ≤ 2 * (δ ^ 2 * vecMass y) +
        2 * (4 * vecMass ((1 - P) *ᵥ y)) := by
      gcongr
      · calc
          vecMass (((A - 1) * P) *ᵥ y) ≤
              ‖(A - 1) * P‖ ^ 2 * vecMass y := vecMass_mulVec_le _ _
          _ ≤ δ ^ 2 * vecMass y := by
            gcongr
            exact pow_le_pow_left (norm_nonneg _) hfix 2
      · calc
          vecMass ((A - 1) *ᵥ ((1 - P) *ᵥ y)) ≤
              ‖A - 1‖ ^ 2 * vecMass ((1 - P) *ᵥ y) :=
            vecMass_mulVec_le _ _
          _ ≤ 4 * vecMass ((1 - P) *ᵥ y) := by
            have hsquare : ‖A - 1‖ ^ 2 ≤ (2 : ℝ) ^ 2 :=
              pow_le_pow_left (norm_nonneg _) hAone 2
            norm_num at hsquare ⊢
            exact mul_le_mul_of_nonneg_right hsquare
              (vecMass_nonneg ((1 - P) *ᵥ y))
    _ ≤ (2 * δ ^ 2 + 16 * ε ^ 2) * vecMass x + 16 * κ := by
      rw [hyMass]
      nlinarith [hcompMass]

/-! ## Translation back to the original matrix model -/

/-- A unitary matrix has Frobenius mass equal to the matrix dimension. -/
theorem vecMass_rowVec_unitary {U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) :
    vecMass (rowVec U) = Fintype.card Y := by
  rw [vecMass, sum_normSq_rowVec]
  exact sum_normSq_of_unitary Y hU

/-- The vector-chain estimate expressed as normalized Hilbert--Schmidt
displacement of a transported matrix.

Here `P` lives on the row-vectorized matrix Hilbert space `Y × Y`,
`T = Ad(Uₜ)`, `A = Ad(Uₐ)`, and `D = Uₜ C Uₜᴴ`.  The capture
error is normalized by `card Y`, exactly as required by hyperlinearity. -/
theorem conjugated_transport_hsDistSq_le
    (hY : 0 < Fintype.card Y)
    {Ua Ut C : Matrix Y Y ℂ}
    (hUa : Ua ∈ Matrix.unitaryGroup Y ℂ)
    (hUt : Ut ∈ Matrix.unitaryGroup Y ℂ)
    (hC : C ∈ Matrix.unitaryGroup Y ℂ)
    {P : Matrix (Y × Y) (Y × Y) ℂ}
    (hP : IsOrthogonalProjectionMatrix P)
    {δ ε κ : ℝ}
    (hfix : ‖(conjDouble Ua - 1) * P‖ ≤ δ)
    (hreverse : ‖(1 - P) * (conjDouble Ut * P * (conjDouble Ut)ᴴ)‖ ≤ ε)
    (hcapture : vecMass ((1 - P) *ᵥ rowVec C) ≤
      κ * Fintype.card Y) :
    hsDistSq Y (Ua * (Ut * C * Utᴴ) * Uaᴴ) (Ut * C * Utᴴ) ≤
      2 * δ ^ 2 + 16 * ε ^ 2 + 16 * κ := by
  letI : Nonempty Y := Fintype.card_pos_iff.mp hY
  let D : Matrix Y Y ℂ := Ut * C * Utᴴ
  have hT : conjDouble Ut ∈ Matrix.unitaryGroup (Y × Y) ℂ :=
    conjDouble_mem_unitaryGroup hUt
  have hA : conjDouble Ua ∈ Matrix.unitaryGroup (Y × Y) ℂ :=
    conjDouble_mem_unitaryGroup hUa
  have hYprod : 0 < Fintype.card (Y × Y) :=
    Fintype.card_pos_iff.mpr inferInstance
  have hchain := transported_displacement_le hYprod hP hT hA hfix hreverse
    hcapture
  have hrow : conjDouble Ut *ᵥ rowVec C = rowVec D := by
    rw [conjDouble_mulVec_rowVec]
  have hdisp : conjDouble Ua *ᵥ (conjDouble Ut *ᵥ rowVec C) -
      conjDouble Ut *ᵥ rowVec C =
      rowVec (Ua * D * Uaᴴ - D) := by
    rw [hrow, conjDouble_mulVec_rowVec]
    rfl
  rw [hdisp, vecMass, sum_normSq_rowVec, vecMass_rowVec_unitary hC] at hchain
  show (∑ i : Y, ∑ j : Y,
      Complex.normSq ((Ua * D * Uaᴴ) i j - D i j)) /
      Fintype.card Y ≤ _
  rw [div_le_iff₀ (by exact_mod_cast hY)]
  calc
    ∑ i : Y, ∑ j : Y,
        Complex.normSq ((Ua * D * Uaᴴ) i j - D i j) ≤
        (2 * δ ^ 2 + 16 * ε ^ 2) * Fintype.card Y +
          16 * (κ * Fintype.card Y) := hchain
    _ = (2 * δ ^ 2 + 16 * ε ^ 2 + 16 * κ) * Fintype.card Y := by ring

/-! ## From conjugation displacement to the marked commutator -/

/-- If two unitaries are close in normalized Hilbert--Schmidt distance, their
commutator is close to the identity.  The squared constant `4` is
dimension-independent. -/
theorem hsDistSq_commutator_le_four (hY : 0 < Fintype.card Y)
    {D E : Matrix Y Y ℂ}
    (hD : D ∈ Matrix.unitaryGroup Y ℂ)
    (hE : E ∈ Matrix.unitaryGroup Y ℂ) :
    hsDistSq Y (D * E * Dᴴ * Eᴴ) 1 ≤ 4 * hsDistSq Y E D := by
  have hDD : D * Dᴴ = 1 := Unitary.mul_star_self_of_mem hD
  have hdecomp : D * E * Dᴴ * Eᴴ - 1 =
      D * (E - D) * Dᴴ * Eᴴ + D * (Eᴴ - Dᴴ) := by
    noncomm_ring [hDD]
  have hterm1 : hsNormSq Y (D * (E - D) * Dᴴ * Eᴴ) =
      hsNormSq Y (E - D) := by
    have hright : Dᴴ * Eᴴ ∈ Matrix.unitaryGroup Y ℂ :=
      mul_mem (star_mem hD) (star_mem hE)
    rw [show D * (E - D) * Dᴴ * Eᴴ =
      D * ((E - D) * (Dᴴ * Eᴴ)) by noncomm_ring]
    rw [hsNormSq_mul_left Y hD hY, hsNormSq_mul_right Y hright]
  have hterm2 : hsNormSq Y (D * (Eᴴ - Dᴴ)) =
      hsNormSq Y (Eᴴ - Dᴴ) := hsNormSq_mul_left Y hD hY _
  change hsNormSq Y (D * E * Dᴴ * Eᴴ - 1) ≤
    4 * hsNormSq Y (E - D)
  rw [hdecomp]
  calc
    hsNormSq Y (D * (E - D) * Dᴴ * Eᴴ + D * (Eᴴ - Dᴴ)) ≤
        2 * hsNormSq Y (D * (E - D) * Dᴴ * Eᴴ) +
          2 * hsNormSq Y (D * (Eᴴ - Dᴴ)) := hsNormSq_add_le _ _ _
    _ = 2 * hsNormSq Y (E - D) + 2 * hsNormSq Y (Eᴴ - Dᴴ) := by
      rw [hterm1, hterm2]
    _ = 4 * hsNormSq Y (E - D) := by
      rw [← Matrix.conjTranspose_sub, hsNormSq_conjTranspose]
      ring

/-- Combined finite-stage bound for the actual marked commutator built from
`D = Uₜ C Uₜᴴ` and `E = Uₐ D Uₐᴴ`. -/
theorem marked_commutator_hsDistSq_le
    (hY : 0 < Fintype.card Y)
    {Ua Ut C : Matrix Y Y ℂ}
    (hUa : Ua ∈ Matrix.unitaryGroup Y ℂ)
    (hUt : Ut ∈ Matrix.unitaryGroup Y ℂ)
    (hC : C ∈ Matrix.unitaryGroup Y ℂ)
    {P : Matrix (Y × Y) (Y × Y) ℂ}
    (hP : IsOrthogonalProjectionMatrix P)
    {δ ε κ : ℝ}
    (hfix : ‖(conjDouble Ua - 1) * P‖ ≤ δ)
    (hreverse : ‖(1 - P) * (conjDouble Ut * P * (conjDouble Ut)ᴴ)‖ ≤ ε)
    (hcapture : vecMass ((1 - P) *ᵥ rowVec C) ≤
      κ * Fintype.card Y) :
    let D := Ut * C * Utᴴ
    let E := Ua * D * Uaᴴ
    hsDistSq Y (D * E * Dᴴ * Eᴴ) 1 ≤
      8 * δ ^ 2 + 64 * ε ^ 2 + 64 * κ := by
  dsimp only
  let D : Matrix Y Y ℂ := Ut * C * Utᴴ
  let E : Matrix Y Y ℂ := Ua * D * Uaᴴ
  have hD : D ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem (mul_mem hUt hC) (star_mem hUt)
  have hE : E ∈ Matrix.unitaryGroup Y ℂ :=
    mul_mem (mul_mem hUa hD) (star_mem hUa)
  have hdisp := conjugated_transport_hsDistSq_le hY hUa hUt hC hP
    hfix hreverse hcapture
  have hcomm := hsDistSq_commutator_le_four hY hD hE
  dsimp [D, E] at hdisp ⊢
  nlinarith

end MarkedCompressionVectorChain
end GroupApproximation
