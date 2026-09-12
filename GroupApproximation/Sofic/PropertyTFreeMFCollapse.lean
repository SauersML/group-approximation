import GroupApproximation.Criterion.CompressionCentralizerDefect
import GroupApproximation.Sofic.MatricialStabilityRadical
import GroupApproximation.Sofic.MatricialStabilityInstances
import GroupApproximation.Sofic.ProjectionRankFlip
import GroupApproximation.Sofic.FiniteStageRobustGap
import GroupApproximation.Sofic.MFTraceRecognition

/-!
# Property-(T)-free MF collapse

This file separates the exact finite-dimensional obstruction from its
robustness input.  Its matrix endpoint is the finite-multiplicity fact used by
an authenticated Leavitt return: a unitary cannot carry a larger projection
into a smaller one with operator-norm leakage below one.
-/

namespace GroupApproximation
namespace PropertyTFreeMFCollapse

open Matrix MatricialStabilityRadical KazhdanCornerMatrices
open scoped Matrix.Norms.L2Operator

variable {Y : FiniteModel}

/-- Leakage below one makes compression from the range of `p` to the range of
`q` injective, so the rank of `p` cannot exceed the rank of `q`. -/
theorem rank_le_of_norm_one_sub_mul_lt_one {p q : Matrix Y Y ℂ}
    (hp : IsOrthogonalProjectionMatrix p) (_hq : IsOrthogonalProjectionMatrix q)
    (hlt : ‖(1 - q) * p‖ < 1) : p.rank ≤ q.rank := by
  let f : LinearMap.range p.mulVecLin →ₗ[ℂ] LinearMap.range q.mulVecLin :=
    LinearMap.codRestrict _ (q.mulVecLin.comp (LinearMap.range p.mulVecLin).subtype)
      (fun x ↦ LinearMap.mem_range_self _ _)
  have hf_apply : ∀ x : LinearMap.range p.mulVecLin,
      (f x : Y → ℂ) = q *ᵥ (x : Y → ℂ) := fun _ ↦ rfl
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine (Submodule.eq_bot_iff _).2 fun x hx ↦ ?_
    have hzero : q *ᵥ (x : Y → ℂ) = 0 := by
      have hker := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      simpa [hf_apply] using hker
    have hfix : p *ᵥ (x : Y → ℂ) = (x : Y → ℂ) :=
      mulVec_eq_self_of_mem_range hp x.2
    have hval : ((1 - q) * p) *ᵥ (x : Y → ℂ) = (x : Y → ℂ) := by
      rw [← Matrix.mulVec_mulVec, hfix, Matrix.sub_mulVec, Matrix.one_mulVec, hzero,
        sub_zero]
    have hbound := sum_normSq_mulVec_le_general ((1 - q) * p) (x : Y → ℂ)
    rw [hval] at hbound
    have hnn : 0 ≤ ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) :=
      Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
    have hsq : ‖(1 - q) * p‖ ^ 2 < 1 := by
      nlinarith [norm_nonneg ((1 - q) * p)]
    have hle : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) ≤ 0 := by
      nlinarith
    have hsum : ∑ i : Y, Complex.normSq ((x : Y → ℂ) i) = 0 :=
      le_antisymm hle hnn
    have hxz : (x : Y → ℂ) = 0 := by
      funext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) ↦ Complex.normSq_nonneg
          ((x : Y → ℂ) j))).mp hsum i (Finset.mem_univ i)
      exact Complex.normSq_eq_zero.mp hi
    exact Subtype.ext hxz
  exact LinearMap.finrank_le_finrank_of_injective hf_inj

/-- Right multiplication by a unitary preserves the matrix operator norm. -/
theorem norm_mul_unitary {A U : Matrix Y Y ℂ}
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) : ‖A * U‖ = ‖A‖ := by
  have hUs : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  have hUU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  apply le_antisymm
  · exact (norm_mul_le A U).trans (by
      have := MFTraceRecognition.norm_unitary_le_one hU
      nlinarith [norm_nonneg A])
  · have hle := norm_mul_le (A * U) Uᴴ
    rw [Matrix.mul_assoc, hUU, Matrix.mul_one] at hle
    have hUsmall := MFTraceRecognition.norm_unitary_le_one hUs
    nlinarith [norm_nonneg (A * U)]

/-- **Rectangular leakage theorem.**  A unitary sends a larger projection
through a smaller projection with leakage exactly one. -/
theorem rectangular_leakage_eq_one {e f U : Matrix Y Y ℂ}
    (he : IsOrthogonalProjectionMatrix e) (hf : IsOrthogonalProjectionMatrix f)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hrank : f.rank < e.rank) :
    ‖(1 - f) * U * e‖ = 1 := by
  have hUs : Uᴴ ∈ Matrix.unitaryGroup Y ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact Unitary.star_mul_self_of_mem hU
  let p : Matrix Y Y ℂ := U * e * Uᴴ
  have hp : IsOrthogonalProjectionMatrix p :=
    unitary_conjugate_isOrthogonalProjection hU he
  have hprank : p.rank = e.rank := rank_unitary_conj hU e
  have hnorm : ‖((1 - f) * U * e) * Uᴴ‖ = ‖(1 - f) * U * e‖ :=
    norm_mul_unitary hUs
  have hrewrite : ((1 - f) * U * e) * Uᴴ = (1 - f) * p := by
    simp only [p]
    noncomm_ring
  have hnot : ¬ ‖(1 - f) * U * e‖ < 1 := by
    intro hlt
    have hlt' : ‖(1 - f) * p‖ < 1 := by rwa [← hrewrite, hnorm]
    have hle := rank_le_of_norm_one_sub_mul_lt_one hp hf hlt'
    rw [hprank] at hle
    exact (Nat.not_le_of_lt hrank) hle
  have heNorm := FiniteStageRobustGap.norm_projection_le_one
    (Y := Y) he
  have hfNorm := FiniteStageRobustGap.norm_projection_le_one
    (Y := Y) (one_sub_isOrthogonalProjection hf)
  have hUNorm := MFTraceRecognition.norm_unitary_le_one hU
  have hupper : ‖(1 - f) * U * e‖ ≤ 1 := by
    calc
      ‖(1 - f) * U * e‖ ≤ ‖1 - f‖ * ‖U‖ * ‖e‖ := by
        exact (norm_mul_le ((1 - f) * U) e).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le (1 - f) U) (norm_nonneg e))
      _ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  exact le_antisymm hupper (le_of_not_gt hnot)

/-- The binary-refinement form: a coarse atom of twice the fine atom's rank
has unit operator-norm leakage through every unitary return. -/
theorem binary_rectangular_leakage_eq_one {e f U : Matrix Y Y ℂ}
    (he : IsOrthogonalProjectionMatrix e) (hf : IsOrthogonalProjectionMatrix f)
    (hU : U ∈ Matrix.unitaryGroup Y ℂ) (hbinary : e.rank = 2 * f.rank)
    (hfpos : 0 < f.rank) : ‖(1 - f) * U * e‖ = 1 := by
  apply rectangular_leakage_eq_one he hf hU
  omega

/-! ## Authentication and the local robustness bridge -/

universe u

/-- A mark has an authenticated rectangular return when every standard
matrix-corona representation which detects it exposes, in one actual finite
coordinate, a larger source projection, a smaller target projection, and a
unitary return with leakage below one.

This is the exact interface required from a concrete finite-coordinate
Leavitt decoder.  It is deliberately a property, not an axiom and not a
purported construction: a concrete presentation must prove this predicate. -/
def HasAuthenticatedRectangularReturn {G : Type u} [Group G] (z : G) : Prop :=
  ∀ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) →
    ∀ rho : G →* NormMatrixCoronaUnitary X, rho z ≠ 1 →
      ∃ (n : ℕ) (e f U : Matrix (X n) (X n) ℂ),
        IsOrthogonalProjectionMatrix e ∧
        IsOrthogonalProjectionMatrix f ∧
        U ∈ Matrix.unitaryGroup (X n) ℂ ∧
        f.rank < e.rank ∧
        ‖(1 - f) * U * e‖ < 1

/-- One authenticated rectangular return makes the marked element invisible
in every standard norm-matrix corona. -/
theorem mem_coronaMFResidual_of_authenticatedRectangularReturn
    {G : Type u} [Group G] {z : G}
    (hauth : HasAuthenticatedRectangularReturn z) :
    z ∈ coronaMFResidual G := by
  rw [mem_coronaMFResidual_iff]
  intro X hX rho
  by_contra hne
  obtain ⟨n, e, f, U, he, hf, hU, hrank, hlt⟩ := hauth X hX rho hne
  have hone := rectangular_leakage_eq_one he hf hU hrank
  linarith

/-- The authenticated return places the mark in the manuscript's literal
genuine-C-star-corona radical as well. -/
theorem mem_actualCoronaMFResidual_of_authenticatedRectangularReturn
    {G : Type u} [Group G] {z : G}
    (hauth : HasAuthenticatedRectangularReturn z) :
    z ∈ actualCoronaMFResidual G := by
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  exact mem_coronaMFResidual_of_authenticatedRectangularReturn hauth

/-- Normal generation turns one authenticated rank-decreasing return into
total MF collapse. -/
theorem actualCoronaMFResidual_eq_top_of_authenticatedRectangularReturn
    {G : Type u} [Group G] {z : G}
    (hauth : HasAuthenticatedRectangularReturn z)
    (hgen : Subgroup.normalClosure ({z} : Set G) = ⊤) :
    actualCoronaMFResidual G = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal
    (Set.singleton_subset_iff.mpr
      (mem_actualCoronaMFResidual_of_authenticatedRectangularReturn hauth))

/-- A nontrivial authenticated mark obstructs operator-MF, before any normal
generation argument is used. -/
theorem not_isOperatorMF_of_authenticatedRectangularReturn
    {G : Type u} [Group G] [Countable G] {z : G} (hz : z ≠ 1)
    (hauth : HasAuthenticatedRectangularReturn z) : ¬ IsOperatorMF G := by
  intro hMF
  have hbot : coronaMFResidual G = ⊥ :=
    isOperatorMF_iff_coronaMFResidual_eq_bot.mp hMF
  have hmem := mem_coronaMFResidual_of_authenticatedRectangularReturn hauth
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz hmem

/-- **Structural Property-(T)-free collapse theorem.**  One authenticated
finite-coordinate return with a rank drop kills the mark; if that mark
normally generates, the literal MF radical is the whole group. -/
theorem authenticatedRectangularReturn_totalCollapse
    {G : Type u} [Group G] [Countable G] {z : G} (hz : z ≠ 1)
    (hauth : HasAuthenticatedRectangularReturn z)
    (hgen : Subgroup.normalClosure ({z} : Set G) = ⊤) :
    actualCoronaMFResidual G = ⊤ ∧ ¬ IsOperatorMF G :=
  ⟨actualCoronaMFResidual_eq_top_of_authenticatedRectangularReturn hauth hgen,
    not_isOperatorMF_of_authenticatedRectangularReturn hz hauth⟩

/-- Exactification only at one marked element.  No approximation is required
at any other group element. -/
def IsFDStableAtMark {G : Type u} [Group G] (z : G) : Prop :=
  ∀ B : OpAlmostRepresentation G,
    ∃ pi : ∀ n, G →* Matrix.unitaryGroup (B.model n) ℂ,
      ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
        ‖(B.map n z : Matrix (B.model n) (B.model n) ℂ) -
          (pi n z : Matrix (B.model n) (B.model n) ℂ)‖ ≤ ε

/-- **Marked stability transfer.**  Finite-dimensional blindness plus
point-norm exactification at the marked element alone implies MF
invisibility.  Approximate multiplicativity automatically pins the image of
the identity, so stability at `1` is not part of the hypothesis. -/
theorem mem_coronaMFResidual_of_mem_fdUnitaryResidual_of_stableAtMark
    {G : Type u} [Group G] [Countable G] {z : G}
    (hfd : z ∈ MatricialStabilityRadical.fdUnitaryResidual G)
    (hstable : IsFDStableAtMark z) : z ∈ coronaMFResidual G := by
  rw [mem_coronaMFResidual_iff]
  intro X hX rho
  by_contra hne
  obtain ⟨A⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one X rho hne
  obtain ⟨pi, hpi⟩ := hstable A.toOpAlmostRepresentation
  have hδ := A.separation_pos
  obtain ⟨Nz, hNz⟩ := hpi (A.separation / 3) (by linarith)
  obtain ⟨N1, hN1⟩ :=
    MatricialStabilityInstances.eventually_norm_map_one_sub_one_le
      A.toOpAlmostRepresentation (by linarith : 0 < A.separation / 3)
  set n := max Nz N1
  have hz := hNz n (le_max_left _ _)
  have hmapOne := hN1 n (le_max_right _ _)
  have hπz : pi n z = 1 :=
    MatricialStabilityRadical.mem_fdUnitaryResidual_iff.mp hfd (A.model n) (pi n)
  have hsep := A.marked_separated n
  have htri :
      ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ ≤
        ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) -
          (pi n z : Matrix (A.model n) (A.model n) ℂ)‖ +
        ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
    calc
      ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ =
          dist (A.map n z : Matrix (A.model n) (A.model n) ℂ)
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) :=
        (dist_eq_norm _ _).symm
      _ ≤ dist (A.map n z : Matrix (A.model n) (A.model n) ℂ)
            (pi n z : Matrix (A.model n) (A.model n) ℂ) +
          dist (pi n z : Matrix (A.model n) (A.model n) ℂ)
            (A.map n 1 : Matrix (A.model n) (A.model n) ℂ) :=
        dist_triangle _ _ _
      _ = ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) -
            (pi n z : Matrix (A.model n) (A.model n) ℂ)‖ +
          ‖(A.map n 1 : Matrix (A.model n) (A.model n) ℂ) - 1‖ := by
        rw [dist_eq_norm, dist_eq_norm, hπz]
        congr 1
        exact norm_sub_rev _ _
  have hlt :
      ‖(A.map n z : Matrix (A.model n) (A.model n) ℂ) - A.map n 1‖ <
        A.separation := by
    calc
      _ ≤ _ := htri
      _ ≤ A.separation / 3 + A.separation / 3 := add_le_add hz hmapOne
      _ < A.separation := by linarith
  exact absurd hsep (not_le_of_gt hlt)

/-! ## Compression plus stability -/

/-- A unitary matrix representation, read as a linear representation. -/
def unitaryLinearEquivHom {G : Type u} [Group G] (Y : FiniteModel)
    (φ : G →* Matrix.unitaryGroup Y ℂ) : G →* ((Y → ℂ) ≃ₗ[ℂ] (Y → ℂ)) where
  toFun g := Matrix.UnitaryGroup.toLinearEquiv (φ g)
  map_one' := by
    rw [map_one]
    ext x i
    simp [Matrix.UnitaryGroup.toLinearEquiv]
  map_mul' g h := by
    rw [map_mul]
    ext x i
    simp [Matrix.UnitaryGroup.toLinearEquiv, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec]

/-- Exact compression collapse puts the intrinsic defect in the
finite-dimensional unitary residual. -/
theorem compressionCentralizerDefect_le_fdUnitaryResidual
    {G : Type u} [Group G] (L : Subgroup G) :
    compressionCentralizerDefect L ≤ fdUnitaryResidual G := by
  intro x hx
  rw [mem_fdUnitaryResidual_iff]
  intro Y φ
  have hk := compressionCentralizerDefect_le_ker (unitaryLinearEquivHom Y φ) L hx
  have heq := (unitaryLinearEquivHom Y φ).mem_ker.mp hk
  change Matrix.UnitaryGroup.toLinearEquiv (φ x) = 1 at heq
  have hlin : Matrix.toLin' (φ x : Matrix Y Y ℂ) = LinearMap.id := by
    simpa [Matrix.UnitaryGroup.toLinearEquiv] using
      congrArg LinearEquiv.toLinearMap heq
  apply Subtype.ext
  rw [← Matrix.toLin'_one] at hlin
  have hmatrix := congrArg LinearMap.toMatrix' hlin
  simpa using hmatrix

/-- **Property-(T)-free compression theorem.**  Point-norm matricial
stability transports the entire intrinsic compression defect into the MF
radical. -/
theorem compressionCentralizerDefect_le_actualCoronaMFResidual
    {G : Type u} [Group G] [Countable G]
    (hstab : IsPointNormMatriciallyStable G) (L : Subgroup G) :
    compressionCentralizerDefect L ≤ actualCoronaMFResidual G := by
  rw [actualCoronaMFResidual_eq_fdUnitaryResidual hstab]
  exact compressionCentralizerDefect_le_fdUnitaryResidual L

/-- A nontrivial compression defect obstructs operator-MF without any
Property `(T)` hypothesis. -/
theorem not_isOperatorMF_of_stable_of_compressionDefect_ne_bot
    {G : Type u} [Group G] [Countable G]
    (hstab : IsPointNormMatriciallyStable G) (L : Subgroup G)
    (hne : compressionCentralizerDefect L ≠ ⊥) : ¬ IsOperatorMF G := by
  intro hMF
  have hfd : fdUnitaryResidual G ≠ ⊥ := by
    intro hbot
    apply hne
    apply le_antisymm
    · rw [← hbot]
      exact compressionCentralizerDefect_le_fdUnitaryResidual L
    · exact bot_le
  exact MatricialStabilityRadical.not_isCDEOperatorMF_of_stable_of_fdResidual_ne_bot
    hstab hfd ((isCDEOperatorMF_iff_isOperatorMF G).mpr hMF)

/-- A full compression defect makes the full group MF-invisible. -/
theorem actualCoronaMFResidual_eq_top_of_stable_of_compressionDefect_eq_top
    {G : Type u} [Group G] [Countable G]
    (hstab : IsPointNormMatriciallyStable G) (L : Subgroup G)
    (hfull : compressionCentralizerDefect L = ⊤) :
    actualCoronaMFResidual G = ⊤ := by
  apply top_unique
  rw [← hfull]
  exact compressionCentralizerDefect_le_actualCoronaMFResidual hstab L

/-- It is enough that an arbitrary set inside the compression defect normally
generates the group; equality of the defect with `⊤` is not an extra input. -/
theorem actualCoronaMFResidual_eq_top_of_stable_of_normalGeneratingSubset
    {G : Type u} [Group G] [Countable G]
    (hstab : IsPointNormMatriciallyStable G) (L : Subgroup G) (S : Set G)
    (hS : S ⊆ compressionCentralizerDefect L)
    (hgen : Subgroup.normalClosure S = ⊤) :
    actualCoronaMFResidual G = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subgroup.normalClosure_le_normal
  intro x hx
  exact compressionCentralizerDefect_le_actualCoronaMFResidual hstab L (hS hx)

/-- **Stable compression criterion.**  Point-norm matricial stability puts
the intrinsic compression defect in the literal MF radical.  A nontrivial
defect obstructs operator-MF, and a full defect makes every genuine matrix
corona homomorphism trivial. -/
theorem stable_compression_criterion
    {G : Type u} [Group G] [Countable G]
    (hstab : IsPointNormMatriciallyStable G) (L : Subgroup G) :
    compressionCentralizerDefect L ≤ actualCoronaMFResidual G ∧
      (compressionCentralizerDefect L ≠ ⊥ → ¬ IsOperatorMF G) ∧
      (compressionCentralizerDefect L = ⊤ →
        actualCoronaMFResidual G = ⊤) :=
  ⟨compressionCentralizerDefect_le_actualCoronaMFResidual hstab L,
    not_isOperatorMF_of_stable_of_compressionDefect_ne_bot hstab L,
    actualCoronaMFResidual_eq_top_of_stable_of_compressionDefect_eq_top
      hstab L⟩

/-! ## Closed audit package -/

/-- The unconditional theorem package proved in this file.  The authenticated
return clause is a universal implication: this package does not assert the
still-open concrete Leavitt decoder. -/
def UnconditionalPropertyTFreeMFCollapsePackage : Prop :=
  (∀ (Y : FiniteModel) (e f U : Matrix Y Y ℂ),
      IsOrthogonalProjectionMatrix e →
      IsOrthogonalProjectionMatrix f →
      U ∈ Matrix.unitaryGroup Y ℂ → f.rank < e.rank →
      ‖(1 - f) * U * e‖ = 1) ∧
  (∀ {G : Type} [Group G] [Countable G] {z : G},
      z ∈ fdUnitaryResidual G → IsFDStableAtMark z →
      z ∈ coronaMFResidual G) ∧
  (∀ {G : Type} [Group G] [Countable G] {z : G},
      z ≠ 1 → HasAuthenticatedRectangularReturn z →
      Subgroup.normalClosure ({z} : Set G) = ⊤ →
      actualCoronaMFResidual G = ⊤ ∧ ¬ IsOperatorMF G) ∧
  (∀ {G : Type} [Group G] [Countable G] (L : Subgroup G) (S : Set G),
      IsPointNormMatriciallyStable G →
      S ⊆ compressionCentralizerDefect L →
      Subgroup.normalClosure S = ⊤ →
      actualCoronaMFResidual G = ⊤)

/-- Closed, axiom-auditable witness for the complete unconditional package. -/
theorem unconditionalPropertyTFreeMFCollapsePackage :
    UnconditionalPropertyTFreeMFCollapsePackage := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Y e f U he hf hU hrank
    exact rectangular_leakage_eq_one he hf hU hrank
  · intro G _ _ z hfd hstable
    exact mem_coronaMFResidual_of_mem_fdUnitaryResidual_of_stableAtMark hfd hstable
  · intro G _ _ z hz hauth hgen
    exact authenticatedRectangularReturn_totalCollapse hz hauth hgen
  · intro G _ _ L S hstable hS hgen
    exact actualCoronaMFResidual_eq_top_of_stable_of_normalGeneratingSubset
      hstable L S hS hgen

end PropertyTFreeMFCollapse
end GroupApproximation
