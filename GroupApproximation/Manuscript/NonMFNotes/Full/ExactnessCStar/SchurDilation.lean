import GroupApproximation.Manuscript.NonMFNotes.Full.ExactnessCStar.WeightKernel
import GroupApproximation.Analysis.VonNeumannTwistedAmplification
import GroupApproximation.Analysis.LanceMultiplicationOperator

/-!
# The Stinespring dilation of a property-A Schur multiplier

Source: `non_mf_group_notes.tex`, section `sec:Esofic`, paragraph
"Exactness": for a discrete group with property A the reduced group
C⋆-algebra is exact \cite{KWExact}.  The Kirchberg--Wassermann / Ozawa
argument compresses the amplified regular representation `c ↦ c ⊗ 1` on
`ℓ²(G; ℓ²(G))` by the column isometry built from the square roots of the
property-A measures.  This file builds the ingredients:

* `ampStarAlgHom` --- the amplification `x ↦ x ⊗ 1` as a ⋆-algebra
  homomorphism `B(H) → B(ℓ²(α; H))`;
* `ampRegRep` --- the amplified regular representation of `C*_r(G)`;
* `schurColumn W x` --- multiplication by `s ↦ √(w(s⁻¹, x))` on `ℓ²(G)`;
* `schurDilation W` --- the contraction `f ↦ (schurColumn W x f)_x` from
  `ℓ²(G)` to `ℓ²(G; ℓ²(G))`, `‖schurDilation W‖ ≤ 1`.
-/

namespace GroupApproximation.Full.NN09c

open GroupApproximation.ExactnessPermanence GroupApproximation.ReducedGroupCStarTrace
open GroupApproximation.TwistedTensor
open scoped ENNReal

universe u v

noncomputable section

section L2

variable {α : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `‖f‖² = ∑' i, ‖f i‖²` in `ℓ²(α; H)`. -/
theorem norm_sq_eq_tsum_vec (f : VecHilbert α H) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem summable_norm_sq_vec (f : VecHilbert α H) : Summable fun i ↦ ‖f i‖ ^ 2 := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp f)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

end L2

section Amp

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The amplification `x ↦ x ⊗ 1`, as a ⋆-algebra homomorphism
`B(H) → B(ℓ²(α; H))`. -/
def ampStarAlgHom (α : Type u) :
    (H →L[ℂ] H) →⋆ₐ[ℂ] (VecHilbert α H →L[ℂ] VecHilbert α H) where
  toFun := ampOperator α
  map_one' := ampOperator_one
  map_mul' := ampOperator_mul
  map_zero' := ContinuousLinearMap.ext fun _ ↦ lp.ext (funext fun _ ↦ rfl)
  map_add' _ _ := ContinuousLinearMap.ext fun _ ↦ lp.ext (funext fun _ ↦ rfl)
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact ContinuousLinearMap.ext fun _ ↦ lp.ext (funext fun _ ↦ rfl)
  map_star' x := (star_ampOperator x).symm

theorem ampStarAlgHom_apply (α : Type u) (x : H →L[ℂ] H) (F : VecHilbert α H) (a : α) :
    ampStarAlgHom α x F a = x (F a) :=
  rfl

end Amp

section Rep

variable (G : Type u) [Group G]

/-- The amplified regular representation `c ↦ c ⊗ 1` of `C*_r(G)` on
`ℓ²(G; ℓ²(G))`. -/
def ampRegRep :
    ReducedGroupCStar G →⋆ₐ[ℂ]
      (VecHilbert G (GroupHilbert G) →L[ℂ] VecHilbert G (GroupHilbert G)) :=
  (ampStarAlgHom G).comp (reducedGroupCStarSubalgebra G).subtype

theorem ampRegRep_apply (c : ReducedGroupCStar G) (F : VecHilbert G (GroupHilbert G))
    (x : G) :
    ampRegRep G c F x = (c : GroupHilbert G →L[ℂ] GroupHilbert G) (F x) :=
  rfl

end Rep

section Column

variable {G : Type u} [Group G] {R : Finset G} {ε : ℝ}

/-- The symbol `s ↦ √(w(s⁻¹, x))` of the `x`-th column of the dilation. -/
def schurSymbol (W : PropertyAWitness G R ε) (x s : G) : ℂ :=
  ((Real.sqrt (W.weight s⁻¹ x) : ℝ) : ℂ)

theorem norm_schurSymbol_le (W : PropertyAWitness G R ε) (x s : G) :
    ‖schurSymbol W x s‖ ≤ 1 := by
  rw [schurSymbol, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr (weight_le_one W s⁻¹ x)

/-- The `x`-th column: multiplication by `s ↦ √(w(s⁻¹, x))` on `ℓ²(G)`. -/
def schurColumn (W : PropertyAWitness G R ε) (x : G) :
    GroupHilbert G →L[ℂ] GroupHilbert G :=
  CStarExactness.mulOp (schurSymbol W x) 1 (norm_schurSymbol_le W x)

theorem schurColumn_apply (W : PropertyAWitness G R ε) (x : G) (f : GroupHilbert G)
    (s : G) : schurColumn W x f s = schurSymbol W x s * f s :=
  rfl

theorem norm_sq_schurColumn_apply (W : PropertyAWitness G R ε) (x : G)
    (f : GroupHilbert G) (s : G) :
    ‖schurColumn W x f s‖ ^ 2 = W.weight s⁻¹ x * ‖f s‖ ^ 2 := by
  rw [schurColumn_apply, norm_mul, schurSymbol, Complex.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (W.weight_nonneg _ _)]

theorem summable_weight_mul_norm_sq (W : PropertyAWitness G R ε) (x : G)
    (f : GroupHilbert G) : Summable fun s ↦ W.weight s⁻¹ x * ‖f s‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (W.weight_nonneg _ _) (sq_nonneg _))
    (fun _ ↦ mul_le_of_le_one_left (sq_nonneg _) (weight_le_one W _ _))
    (summable_norm_sq_vec f)

theorem norm_sq_schurColumn (W : PropertyAWitness G R ε) (x : G) (f : GroupHilbert G) :
    ‖schurColumn W x f‖ ^ 2 = ∑' s, W.weight s⁻¹ x * ‖f s‖ ^ 2 :=
  (norm_sq_eq_tsum_vec (schurColumn W x f)).trans
    (tsum_congr fun s ↦ norm_sq_schurColumn_apply W x f s)

/-- **The columns are square-summable**: `∑_{x ∈ S} ‖schurColumn W x f‖² ≤ ‖f‖²`. -/
theorem sum_norm_sq_schurColumn_le (W : PropertyAWitness G R ε) (f : GroupHilbert G)
    (S : Finset G) : ∑ x ∈ S, ‖schurColumn W x f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  have hsum : ∀ x ∈ S, Summable fun s ↦ W.weight s⁻¹ x * ‖f s‖ ^ 2 :=
    fun x _ ↦ summable_weight_mul_norm_sq W x f
  have hbound : ∀ s : G, (∑ x ∈ S, W.weight s⁻¹ x) * ‖f s‖ ^ 2 ≤ ‖f s‖ ^ 2 :=
    fun s ↦ mul_le_of_le_one_left (sq_nonneg _) (sum_weight_le_one W s⁻¹ S)
  have hsummable : Summable fun s ↦ (∑ x ∈ S, W.weight s⁻¹ x) * ‖f s‖ ^ 2 :=
    Summable.of_nonneg_of_le
      (fun _ ↦ mul_nonneg (Finset.sum_nonneg fun _ _ ↦ W.weight_nonneg _ _) (sq_nonneg _))
      hbound (summable_norm_sq_vec f)
  calc ∑ x ∈ S, ‖schurColumn W x f‖ ^ 2
      = ∑ x ∈ S, ∑' s, W.weight s⁻¹ x * ‖f s‖ ^ 2 :=
        Finset.sum_congr rfl fun x _ ↦ norm_sq_schurColumn W x f
    _ = ∑' s, ∑ x ∈ S, W.weight s⁻¹ x * ‖f s‖ ^ 2 := (Summable.tsum_finsetSum hsum).symm
    _ = ∑' s, (∑ x ∈ S, W.weight s⁻¹ x) * ‖f s‖ ^ 2 :=
        tsum_congr fun s ↦ (Finset.sum_mul S _ _).symm
    _ ≤ ∑' s, ‖f s‖ ^ 2 := Summable.tsum_le_tsum hbound hsummable (summable_norm_sq_vec f)
    _ = ‖f‖ ^ 2 := (norm_sq_eq_tsum_vec f).symm

theorem memℓp_schurColumn (W : PropertyAWitness G R ε) (f : GroupHilbert G) :
    Memℓp (fun x : G ↦ schurColumn W x f) 2 :=
  memℓp_gen' (C := ‖f‖ ^ 2) fun S ↦ by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using sum_norm_sq_schurColumn_le W f S

/-- The dilation `f ↦ (schurColumn W x f)_x`, as a linear map. -/
def schurDilationLinear (W : PropertyAWitness G R ε) :
    GroupHilbert G →ₗ[ℂ] VecHilbert G (GroupHilbert G) where
  toFun f := ⟨fun x ↦ schurColumn W x f, memℓp_schurColumn W f⟩
  map_add' f g := lp.ext (funext fun x ↦ map_add (schurColumn W x) f g)
  map_smul' c f := lp.ext (funext fun x ↦ map_smul (schurColumn W x) c f)

theorem schurDilationLinear_apply (W : PropertyAWitness G R ε) (f : GroupHilbert G)
    (x : G) : schurDilationLinear W f x = schurColumn W x f :=
  rfl

theorem norm_schurDilationLinear_le (W : PropertyAWitness G R ε) (f : GroupHilbert G) :
    ‖schurDilationLinear W f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  refine lp.norm_le_of_forall_sum_le (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (norm_nonneg f)
    fun S ↦ ?_
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, schurDilationLinear_apply] using
    sum_norm_sq_schurColumn_le W f S

/-- **The Schur dilation** `ℓ²(G) → ℓ²(G; ℓ²(G))`, a contraction. -/
def schurDilation (W : PropertyAWitness G R ε) :
    GroupHilbert G →L[ℂ] VecHilbert G (GroupHilbert G) :=
  (schurDilationLinear W).mkContinuous 1 (norm_schurDilationLinear_le W)

theorem schurDilation_apply (W : PropertyAWitness G R ε) (f : GroupHilbert G) (x : G) :
    schurDilation W f x = schurColumn W x f :=
  rfl

theorem norm_schurDilation_le (W : PropertyAWitness G R ε) : ‖schurDilation W‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end Column

end

end GroupApproximation.Full.NN09c
