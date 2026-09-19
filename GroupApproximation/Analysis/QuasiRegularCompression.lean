import GroupApproximation.Analysis.QuasiRegularWitness
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.UCPContractiveMatrix
import GroupApproximation.Analysis.MaximalGroupCStarTrace

/-!
# Finite compressions of quasi-regular representations

For a subgroup `K ≤ G`, a finite model `Y`, and an injective enumeration
`e : Y → G ⧸ K`, this file compresses the quasi-regular representation on
`ℓ²(G/K)` to the point masses named by `e`.  The resulting map from the full
group C-star algebra is unital, completely positive, and contractive.  On a
canonical generator it is the partial permutation matrix of the left action
on the selected cosets.

The incidence and escape formulas are intentionally stated for an arbitrary
`FiniteModel`, so product windows such as `Fin L × (H ⧸ K)` can use them
without first choosing an equivalence with `Fin k`.
-/

namespace GroupApproximation
namespace QuasiRegularCompression

open Filter Matrix ReducedGroupCStarTrace
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u

variable {G : Type u} [Group G]

local instance cosetDecidableEq (K : Subgroup G) : DecidableEq (G ⧸ K) :=
  Classical.decEq (G ⧸ K)

/-! ## Point masses and the evaluated representation -/

/-- The standard basis vector at a coset. -/
def cosetPointMass (K : Subgroup G) (x : G ⧸ K) :
    QuasiRegularWitness.CosetHilbert G K :=
  lp.single 2 x (1 : ℂ)

@[simp] theorem cosetPointMass_def (K : Subgroup G) (x : G ⧸ K) :
    cosetPointMass K x = lp.single 2 x (1 : ℂ) := rfl

/-- The coset point masses are orthonormal. -/
theorem cosetPointMass_inner (K : Subgroup G) (x y : G ⧸ K) :
    ⟪cosetPointMass K x, cosetPointMass K y⟫_ℂ = if x = y then 1 else 0 := by
  rw [cosetPointMass_def, cosetPointMass_def, lp.inner_single_left]
  by_cases h : x = y
  · subst h
    rw [lp.single_apply_self, if_pos rfl]
    simp
  · rw [lp.single_apply_ne _ _ _ h, if_neg h]
    simp

/-- Left quasi-regular translation permutes the coset point masses. -/
theorem quasiRegularOperator_cosetPointMass (K : Subgroup G) (g : G)
    (x : G ⧸ K) :
    QuasiRegularWitness.quasiRegularOperator G K g (cosetPointMass K x) =
      cosetPointMass K (g • x) := by
  apply lp.ext
  funext y
  rw [QuasiRegularWitness.quasiRegularOperator_apply]
  by_cases h : y = g • x
  · subst h
    rw [inv_smul_smul, cosetPointMass_def, cosetPointMass_def,
      lp.single_apply_self, lp.single_apply_self]
  · have h' : g⁻¹ • y ≠ x := by
      intro hxy
      apply h
      rw [← hxy, smul_smul, mul_inv_cancel, one_smul]
    rw [cosetPointMass_def, cosetPointMass_def,
      lp.single_apply_ne _ _ _ h', lp.single_apply_ne _ _ _ h]

/-- Evaluation of `C*(G)` in the quasi-regular representation on `G/K`. -/
def evaluated (K : Subgroup G) :
    MaximalGroupCStar G →⋆ₐ[ℂ]
      (QuasiRegularWitness.CosetHilbert G K →L[ℂ]
        QuasiRegularWitness.CosetHilbert G K) :=
  maximalGroupCStarEval G (QuasiRegularWitness.quasiRegularRepresentation G K)

@[simp] theorem evaluated_generator (K : Subgroup G) (g : G) :
    evaluated K (maximalGroupCStarGenerator G g) =
      QuasiRegularWitness.quasiRegularOperator G K g :=
  maximalGroupCStarEval_generator G
    (QuasiRegularWitness.quasiRegularRepresentation G K) g

/-! ## The compression map -/

/-- Compression of the quasi-regular representation to finitely many cosets. -/
def compressionMap (K : Subgroup G) (Y : FiniteModel) (e : Y → G ⧸ K) :
    MaximalGroupCStar G →ₗ[ℂ] Matrix Y Y ℂ where
  toFun a p q :=
    ⟪cosetPointMass K (e p), evaluated K a (cosetPointMass K (e q))⟫_ℂ
  map_add' a b := by
    funext p q
    show ⟪cosetPointMass K (e p),
        evaluated K (a + b) (cosetPointMass K (e q))⟫_ℂ =
      ⟪cosetPointMass K (e p), evaluated K a (cosetPointMass K (e q))⟫_ℂ +
      ⟪cosetPointMass K (e p), evaluated K b (cosetPointMass K (e q))⟫_ℂ
    rw [map_add, _root_.add_apply, inner_add_right]
  map_smul' c a := by
    funext p q
    show ⟪cosetPointMass K (e p),
        evaluated K (c • a) (cosetPointMass K (e q))⟫_ℂ =
      c * ⟪cosetPointMass K (e p), evaluated K a (cosetPointMass K (e q))⟫_ℂ
    rw [map_smul, _root_.smul_apply, inner_smul_right]

@[simp] theorem compressionMap_apply (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (a : MaximalGroupCStar G) (p q : Y) :
    compressionMap K Y e a p q =
      ⟪cosetPointMass K (e p), evaluated K a (cosetPointMass K (e q))⟫_ℂ :=
  rfl

/-- Injective coset coordinates make the compression unital. -/
theorem compressionMap_one (K : Subgroup G) (Y : FiniteModel)
    {e : Y → G ⧸ K} (he : Function.Injective e) :
    compressionMap K Y e 1 = 1 := by
  funext p q
  rw [compressionMap_apply, map_one]
  show ⟪cosetPointMass K (e p),
      (1 : QuasiRegularWitness.CosetHilbert G K →L[ℂ]
        QuasiRegularWitness.CosetHilbert G K) (cosetPointMass K (e q))⟫_ℂ = _
  rw [one_apply_eq_self, cosetPointMass_inner]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
  · rw [if_neg (fun hc ↦ h (he hc)), Matrix.one_apply_ne h]

/-- The scalar form of a compression is the ambient operator form. -/
theorem compressionMap_form (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (a : MaximalGroupCStar G) (x y : Y → ℂ) :
    (∑ p : Y, ∑ q : Y,
        (starRingEnd ℂ) (x p) * compressionMap K Y e a p q * y q) =
      ⟪∑ p : Y, x p • cosetPointMass K (e p),
        evaluated K a (∑ q : Y, y q • cosetPointMass K (e q))⟫_ℂ := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [map_smul, inner_smul_right, compressionMap_apply]
  ring

/-- Every quasi-regular compression is completely positive. -/
theorem isCompletelyPositiveOnMatrices_compressionMap (K : Subgroup G)
    (Y : FiniteModel) (e : Y → G ⧸ K) :
    Quasidiagonal.IsCompletelyPositiveOnMatrices Y ⇑(compressionMap K Y e) := by
  intro m a w
  let v : Fin m → QuasiRegularWitness.CosetHilbert G K :=
    fun i ↦ ∑ q : Y, w i q • cosetPointMass K (e q)
  let u : QuasiRegularWitness.CosetHilbert G K :=
    ∑ i : Fin m, evaluated K (a i) (v i)
  have hterm : ∀ i j : Fin m,
      (∑ p : Y, ∑ q : Y,
          (starRingEnd ℂ) (w i p) *
            compressionMap K Y e (star (a i) * a j) p q * w j q) =
        ⟪evaluated K (a i) (v i), evaluated K (a j) (v j)⟫_ℂ := by
    intro i j
    rw [compressionMap_form]
    have hco : evaluated K (star (a i) * a j) (v j) =
        ContinuousLinearMap.adjoint (evaluated K (a i))
          (evaluated K (a j) (v j)) := by
      rw [map_mul, map_star]
      rw [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp]
    rw [hco, ContinuousLinearMap.adjoint_inner_right]
  have hgoal :
      (∑ i : Fin m, ∑ j : Fin m, ∑ p : Y, ∑ q : Y,
          (starRingEnd ℂ) (w i p) *
            compressionMap K Y e (star (a i) * a j) p q * w j q) = ⟪u, u⟫_ℂ := by
    change _ = ⟪∑ i : Fin m, evaluated K (a i) (v i),
      ∑ j : Fin m, evaluated K (a j) (v j)⟫_ℂ
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun j _ ↦ hterm i j
  have hself : ⟪u, u⟫_ℂ = ((‖u‖ : ℝ) : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K u
  constructor
  · show (∑ i : Fin m, ∑ j : Fin m, ∑ p : Y, ∑ q : Y,
        (starRingEnd ℂ) (w i p) *
          compressionMap K Y e (star (a i) * a j) p q * w j q).im = 0
    rw [hgoal, hself, ← Complex.ofReal_pow, Complex.ofReal_im]
  · show 0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ p : Y, ∑ q : Y,
        (starRingEnd ℂ) (w i p) *
          compressionMap K Y e (star (a i) * a j) p q * w j q).re
    rw [hgoal, hself, ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

/-- A unital quasi-regular compression is contractive. -/
theorem norm_compressionMap_le (K : Subgroup G) (Y : FiniteModel)
    {e : Y → G ⧸ K} (he : Function.Injective e) (a : MaximalGroupCStar G) :
    ‖compressionMap K Y e a‖ ≤ ‖a‖ :=
  Quasidiagonal.ucp_norm_le (compressionMap K Y e)
    (compressionMap_one K Y he)
    (isCompletelyPositiveOnMatrices_compressionMap K Y e) a

/-! ## Generator incidence, trace, and multiplicative defect -/

/-- The incidence coefficient for the left action on the selected cosets. -/
def incidence (K : Subgroup G) (Y : FiniteModel) (e : Y → G ⧸ K)
    (g : G) (p q : Y) : ℂ :=
  if e p = g • e q then 1 else 0

theorem incidence_eq_one (K : Subgroup G) (Y : FiniteModel)
    {e : Y → G ⧸ K} {g : G} {p q : Y} (h : e p = g • e q) :
    incidence K Y e g p q = 1 := if_pos h

theorem incidence_eq_zero (K : Subgroup G) (Y : FiniteModel)
    {e : Y → G ⧸ K} {g : G} {p q : Y} (h : e p ≠ g • e q) :
    incidence K Y e g p q = 0 := if_neg h

/-- A compressed generator is the incidence matrix of the partial action. -/
theorem compressionMap_generator_apply (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (g : G) (p q : Y) :
    compressionMap K Y e (maximalGroupCStarGenerator G g) p q =
      incidence K Y e g p q := by
  rw [compressionMap_apply, evaluated_generator,
    quasiRegularOperator_cosetPointMass, cosetPointMass_inner]
  rfl

/-- Fixed coordinates of a group element in the selected coset window. -/
def fixedPoints (K : Subgroup G) (Y : FiniteModel) (e : Y → G ⧸ K)
    (g : G) : Finset Y :=
  Finset.univ.filter fun q ↦ e q = g • e q

@[simp] theorem mem_fixedPoints (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (g : G) (q : Y) :
    q ∈ fixedPoints K Y e g ↔ g • e q = e q := by
  simp [fixedPoints, eq_comm]

/-- The normalized trace of a compressed generator is its fixed-point ratio. -/
theorem normTrace_compressionMap_generator (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (g : G) :
    normTrace Y (compressionMap K Y e (maximalGroupCStarGenerator G g)) =
      ((fixedPoints K Y e g).card : ℂ) / (Fintype.card Y : ℂ) := by
  rw [normTrace]
  show (∑ q : Y,
      compressionMap K Y e (maximalGroupCStarGenerator G g) q q) /
        (Fintype.card Y : ℂ) = _
  simp_rw [compressionMap_generator_apply]
  congr 1
  simp only [incidence, fixedPoints, Finset.sum_boole]

/-- The generator trace vanishes when there is no fixed selected coset. -/
theorem normTrace_compressionMap_generator_eq_zero (K : Subgroup G)
    (Y : FiniteModel) (e : Y → G ⧸ K) (g : G)
    (hfix : ∀ q : Y, g • e q ≠ e q) :
    normTrace Y (compressionMap K Y e (maximalGroupCStarGenerator G g)) = 0 := by
  rw [normTrace_compressionMap_generator]
  have hempty : fixedPoints K Y e g = ∅ := by
    ext q
    simp [hfix q]
  rw [hempty]
  simp

/-- Coordinates which leave the selected window under `g`. -/
def escape (K : Subgroup G) (Y : FiniteModel) (e : Y → G ⧸ K)
    (g : G) : Finset Y :=
  Finset.univ.filter fun q ↦ g • e q ∉ Set.range e

@[simp] theorem mem_escape (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (g : G) (q : Y) :
    q ∈ escape K Y e g ↔ g • e q ∉ Set.range e := by
  simp [escape]

/-- The multiplicative defect on a pair of canonical generators. -/
def generatorDefect (K : Subgroup G) (Y : FiniteModel) (e : Y → G ⧸ K)
    (g h : G) : Matrix Y Y ℂ :=
  compressionMap K Y e (maximalGroupCStarGenerator G (g * h)) -
    compressionMap K Y e (maximalGroupCStarGenerator G g) *
      compressionMap K Y e (maximalGroupCStarGenerator G h)

/-- Entrywise formula for the generator defect. -/
theorem generatorDefect_apply (K : Subgroup G) (Y : FiniteModel)
    (e : Y → G ⧸ K) (g h : G) (p q : Y) :
    generatorDefect K Y e g h p q =
      incidence K Y e (g * h) p q -
        ∑ r : Y, incidence K Y e g p r * incidence K Y e h r q := by
  simp only [generatorDefect, Matrix.sub_apply, Matrix.mul_apply,
    compressionMap_generator_apply]

/-- A defect column vanishes whenever the intermediate `h`-translate remains
inside the selected coset window. -/
theorem generatorDefect_apply_of_not_mem_escape (K : Subgroup G)
    (Y : FiniteModel) {e : Y → G ⧸ K} (he : Function.Injective e)
    (g h : G) (p q : Y) (hq : q ∉ escape K Y e h) :
    generatorDefect K Y e g h p q = 0 := by
  rw [generatorDefect_apply]
  have hrange : h • e q ∈ Set.range e := by
    simpa [escape] using hq
  obtain ⟨r, hr⟩ := hrange
  have hsum : (∑ s : Y,
      incidence K Y e g p s * incidence K Y e h s q) =
      incidence K Y e g p r := by
    rw [Finset.sum_eq_single r]
    · rw [incidence_eq_one K Y hr, mul_one]
    · intro s _ hsr
      have hne : e s ≠ h • e q := by
        rw [← hr]
        exact fun hs ↦ hsr (he hs)
      rw [incidence_eq_zero K Y hne, mul_zero]
    · simp
  rw [hsum]
  by_cases hp : e p = (g * h) • e q
  · have hp' : e p = g • e r := by
      calc
        e p = (g * h) • e q := hp
        _ = g • (h • e q) := by rw [smul_smul]
        _ = g • e r := congrArg (fun x ↦ g • x) hr.symm
    rw [incidence_eq_one K Y hp, incidence_eq_one K Y hp', sub_self]
  · have hp' : e p ≠ g • e r := by
      intro hc
      apply hp
      calc
        e p = g • e r := hc
        _ = g • (h • e q) := congrArg (fun x ↦ g • x) hr
        _ = (g * h) • e q := by rw [smul_smul]
    rw [incidence_eq_zero K Y hp, incidence_eq_zero K Y hp', sub_self]

/-- Outside the intermediate window the product term vanishes, so the defect
column is just the `(g*h)` incidence column. -/
theorem generatorDefect_apply_of_mem_escape (K : Subgroup G)
    (Y : FiniteModel) {e : Y → G ⧸ K} (g h : G) (p q : Y)
    (hq : q ∈ escape K Y e h) :
    generatorDefect K Y e g h p q = incidence K Y e (g * h) p q := by
  rw [generatorDefect_apply, sub_eq_self]
  apply Finset.sum_eq_zero
  intro r _
  have hne : e r ≠ h • e q := by
    intro hr
    have : h • e q ∈ Set.range e := ⟨r, hr⟩
    exact (mem_escape K Y e h q).mp hq this
  rw [incidence_eq_zero K Y hne, mul_zero]

/-- The squared normalized Hilbert--Schmidt generator defect is bounded by
the proportion of columns which escape under the second factor. -/
theorem hsNormSq_generatorDefect_le_escape (K : Subgroup G)
    (Y : FiniteModel) {e : Y → G ⧸ K} (he : Function.Injective e)
    (g h : G) :
    hsNormSq Y (generatorDefect K Y e g h) ≤
      (escape K Y e h).card / (Fintype.card Y : ℝ) := by
  have hcol : ∀ q : Y,
      (∑ p : Y, Complex.normSq (generatorDefect K Y e g h p q)) ≤
        if q ∈ escape K Y e h then 1 else 0 := by
    intro q
    by_cases hq : q ∈ escape K Y e h
    · rw [if_pos hq]
      simp_rw [generatorDefect_apply_of_mem_escape K Y g h _ q hq]
      by_cases hex : ∃ p : Y, e p = (g * h) • e q
      · obtain ⟨r, hr⟩ := hex
        rw [Finset.sum_eq_single r]
        · rw [incidence_eq_one K Y hr]
          norm_num
        · intro p _ hpr
          have hp : e p ≠ (g * h) • e q := by
            rw [← hr]
            exact fun hp ↦ hpr (he hp)
          rw [incidence_eq_zero K Y hp]
          norm_num
        · simp
      · have hz : ∀ p : Y, incidence K Y e (g * h) p q = 0 := by
          intro p
          exact incidence_eq_zero K Y (fun hp ↦ hex ⟨p, hp⟩)
        simp_rw [hz]
        norm_num
    · rw [if_neg hq]
      simp_rw [generatorDefect_apply_of_not_mem_escape K Y he g h _ q hq]
      norm_num
  rw [hsNormSq, Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (∑ q : Y, ∑ p : Y, Complex.normSq (generatorDefect K Y e g h p q))
        ≤ ∑ q : Y, if q ∈ escape K Y e h then 1 else 0 :=
      Finset.sum_le_sum fun q _ ↦ hcol q
    _ = (escape K Y e h).card := by
      rw [Finset.sum_boole]
      have hset : (Finset.univ.filter fun q : Y ↦ q ∈ escape K Y e h) =
          escape K Y e h := by
        ext q
        simp
      rw [hset]

/-- The corresponding Hilbert--Schmidt norm bound, in square-root form. -/
theorem hsNorm_generatorDefect_le_sqrt_escape (K : Subgroup G)
    (Y : FiniteModel) {e : Y → G ⧸ K} (he : Function.Injective e)
    (g h : G) :
    hsNorm Y (generatorDefect K Y e g h) ≤
      Real.sqrt ((escape K Y e h).card / (Fintype.card Y : ℝ)) := by
  exact Real.sqrt_le_sqrt (hsNormSq_generatorDefect_le_escape K Y he g h)

end

end QuasiRegularCompression
end GroupApproximation
