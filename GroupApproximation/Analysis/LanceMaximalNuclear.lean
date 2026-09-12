import GroupApproximation.Analysis.LanceMaximalReiter
import GroupApproximation.Analysis.LanceForward
import GroupApproximation.Analysis.MaximalGroupCStarTrace
import GroupApproximation.Analysis.MaximalCStarKazhdanAverage
import GroupApproximation.Analysis.GroupVonNeumannTrace
import GroupApproximation.Analysis.QuasidiagonalMatricialTrace
import GroupApproximation.Algebra.AmenableMean
import GroupApproximation.Meta.AxiomGuard

/-!
# Lance's theorem at the maximal group C⋆-algebra

`isAmenable_of_isNuclearCStarAlgebra_maximalGroupCStar`: if the maximal group
C⋆-algebra `C^*_{\max}(G)` of a discrete group has the completely positive
approximation property of `Analysis/CStarExactness`, then `G` is amenable.

## Why this is not the reduced theorem composed with a quotient

The canonical map `C^*_{\max}(G) → C^*_λ(G)` is onto, but at the approximation
property "nuclearity passes to quotients" is the Choi--Effros lifting theorem,
which the repository does not have (`Analysis/NuclearQuotient`).  The argument
here never forms the quotient.

## The argument

Fix a finite set `F` and a tolerance.  The approximation property gives
completely positive maps `down : C^*_{\max}(G) → M_Y(ℂ)` and
`up : M_Y(ℂ) → C^*_{\max}(G)` with `up (down u_g) ≈ u_g` on `F ∪ F⁻¹ ∪ {1}`.

* `D g = down (u_g)` is positive on pairs (`pairPositive_of_isCompletelyPositive`),
  because `[u_{a_i}⋆ u_{a_j}]` is a positive matrix for `a = (1, g)`.
* The Choi matrix of `up` is positive, so `up (E_{y y'}) = ∑ₖ P_{k y}⋆ P_{k y'}`
  (`exists_choi_factor`), and `up (down u_g) = ∑_{y,y'} D g y y' • up (E_{y y'})`.
* Each `P_{k y}` is approximated by a finite combination `∑ₛ c_{k y}(s) u_s`
  (the generators span a dense subspace).  With these finite families the
  canonical trace `τ` gives, exactly, `τ(u_g⋆ θ(g)) = corr D d g` where `θ` is
  the approximate composite and `d_{k y}(x) = c_{k y}(x⁻¹)`
  (`trace_star_gen_mul_star_mul`): only `τ(u_h) = [h = 1]` is used.
* `|τ(u_g⋆ θ(g)) - 1| ≤ ‖θ(g) - u_g‖`, which is small, so the correlations are
  near `1`, and `Analysis/LanceMaximalReiter` turns that into almost invariant
  unit vectors, hence an invariant mean.

## Manuscript status

Gives the sentence "here `C^*_{\max}(W)` is not nuclear, since `W` is not
amenable" (`non_mf_groups_exist.tex`, introduction) its missing step, at the
corpus-wide nuclearity predicate and with no quotient permanence
(`Manuscript/OneSidedMFRadical/MaximalCStarWNotNuclearUnconditional`).
-/

namespace GroupApproximation
namespace LanceMaximal

open CStarExactness LanceAmenability ReducedGroupCStarTrace
open scoped Matrix.Norms.L2Operator InnerProductSpace

universe u

noncomputable section

attribute [local instance] CStarExactness.matrixBlockCStarAlgebraForLanceForward

/-! ## Pair positivity from complete positivity -/

section Maps

variable {G : Type u} [Group G]

/-- The sesquilinear form of a finite sum of matrices. -/
theorem qform_sum {Y : Type} [Fintype Y] {ι : Type} [Fintype ι]
    (M : ι → Matrix Y Y ℂ) (v w : Y → ℂ) :
    qform (∑ k, M k) v w = ∑ k, qform (M k) v w := by
  simp only [qform, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.sum_comm]

/-- **A completely positive map into a matrix block is positive on pairs** along
any family `u` with `u g⋆ = u g⁻¹` and `u g u h = u (g h)`. -/
theorem pairPositive_of_isCompletelyPositive {A : Type*} [CStarAlgebra A]
    (Y : FiniteModel) [Nonempty Y] (down : A →ₗ[ℂ] Matrix Y Y ℂ)
    (hdown : IsCompletelyPositive down) (u : G → A)
    (hstar : ∀ g, star (u g) = u g⁻¹) (hmul : ∀ g h, u g * u h = u (g * h)) :
    PairPositive (fun g ↦ down (u g)) := by
  intro g v w
  let a : Fin 2 → A := ![u 1, u g]
  let hv : Fin 2 → Y → ℂ := ![v, w]
  obtain ⟨N, hN⟩ := star_col_mul_col a
  obtain ⟨P, hP⟩ := hdown 2 _ ⟨N, hN⟩
  have hent : ∀ i j : Fin 2,
      down (star (a i) * a j) = ∑ k : Fin 2, star (P k i) * P k j := by
    intro i j
    have h : ((CStarMatrix.ofMatrix (Matrix.of fun i j ↦ star (a i) * a j)).map
        ⇑down) i j = (star P * P) i j := by rw [hP]
    rw [cstarMatrix_mul_apply] at h
    have hl : ((CStarMatrix.ofMatrix (Matrix.of fun i j ↦ star (a i) * a j)).map
        ⇑down) i j = down (star (a i) * a j) := rfl
    rw [hl] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [CStarMatrix.star_apply]
  have h00 : star (a 0) * a 0 = u 1 := by
    show star (u 1) * u 1 = u 1
    rw [hstar, hmul, inv_one, one_mul]
  have h01 : star (a 0) * a 1 = u g := by
    show star (u 1) * u g = u g
    rw [hstar, hmul, inv_one, one_mul]
  have h10 : star (a 1) * a 0 = u g⁻¹ := by
    show star (u g) * u 1 = u g⁻¹
    rw [hstar, hmul, mul_one]
  have h11 : star (a 1) * a 1 = u 1 := by
    show star (u g) * u g = u 1
    rw [hstar, hmul, inv_mul_cancel]
  let p : Fin 2 → Fin 2 → Y → ℂ := fun k i t ↦ ∑ x : Y, P k i t x * hv i x
  have hform : ∀ i j : Fin 2,
      qform (down (star (a i) * a j)) (hv i) (hv j) =
        ∑ k : Fin 2, ∑ t : Y, (starRingEnd ℂ) (p k i t) * p k j t := by
    intro i j
    rw [hent i j, qform_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact Quasidiagonal.sum_form_star_mul Y (P k i) (P k j) (hv i) (hv j)
  have hsplit : ∀ k : Fin 2,
      ∑ t : Y, (starRingEnd ℂ) (∑ i : Fin 2, p k i t) * ∑ j : Fin 2, p k j t =
        ∑ t : Y, (starRingEnd ℂ) (p k 0 t) * p k 0 t +
          ∑ t : Y, (starRingEnd ℂ) (p k 0 t) * p k 1 t +
          ∑ t : Y, (starRingEnd ℂ) (p k 1 t) * p k 0 t +
          ∑ t : Y, (starRingEnd ℂ) (p k 1 t) * p k 1 t := by
    intro k
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    simp only [Fin.sum_univ_two, map_add]
    ring
  have e00 := hform 0 0
  have e01 := hform 0 1
  have e10 := hform 1 0
  have e11 := hform 1 1
  rw [h00] at e00
  rw [h01] at e01
  rw [h10] at e10
  rw [h11] at e11
  have htotal : qform (down (u 1)) v v + qform (down (u g)) v w +
      qform (down (u g⁻¹)) w v + qform (down (u 1)) w w =
        ∑ k : Fin 2, ∑ t : Y,
          (starRingEnd ℂ) (∑ i : Fin 2, p k i t) * ∑ j : Fin 2, p k j t := by
    have hv0 : hv 0 = v := rfl
    have hv1 : hv 1 = w := rfl
    rw [hv0] at e00 e01 e10
    rw [hv1] at e01 e10 e11
    rw [e00, e01, e10, e11]
    simp only [hsplit, Finset.sum_add_distrib]
  show 0 ≤ (qform (down (u 1)) v v + qform (down (u g)) v w +
      qform (down (u g⁻¹)) w v + qform (down (u 1)) w w).re
  rw [htotal, Complex.re_sum]
  refine Finset.sum_nonneg fun k _ ↦ ?_
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun t _ ↦ ?_
  rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-- **The Choi factorization of a completely positive map out of a matrix
block**: the images of the matrix units are the entries of `P⋆ P`. -/
theorem exists_choi_factor {A : Type*} [CStarAlgebra A] (Y : FiniteModel)
    [Nonempty Y] (up : Matrix Y Y ℂ →ₗ[ℂ] A) (hup : IsCompletelyPositive up) :
    ∃ P : Fin (Fintype.card Y) → Fin (Fintype.card Y) → A,
      ∀ y y' : Y, up (Matrix.single y y' 1) =
        ∑ k, star (P k (Fintype.equivFin Y y)) * P k (Fintype.equivFin Y y') := by
  haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨y0⟩ := (inferInstance : Nonempty Y)
  let a : Fin (Fintype.card Y) → Matrix Y Y ℂ :=
    fun i ↦ Matrix.single y0 ((Fintype.equivFin Y).symm i) 1
  obtain ⟨N, hN⟩ := star_col_mul_col a
  obtain ⟨P, hP⟩ := hup _ _ ⟨N, hN⟩
  refine ⟨fun k i ↦ P k i, fun y y' ↦ ?_⟩
  have h : ((CStarMatrix.ofMatrix (Matrix.of fun i j ↦ star (a i) * a j)).map ⇑up)
      (Fintype.equivFin Y y) (Fintype.equivFin Y y') =
        (star P * P) (Fintype.equivFin Y y) (Fintype.equivFin Y y') := by
    rw [hP]
  rw [cstarMatrix_mul_apply] at h
  have hl : ((CStarMatrix.ofMatrix (Matrix.of fun i j ↦ star (a i) * a j)).map ⇑up)
      (Fintype.equivFin Y y) (Fintype.equivFin Y y') =
        up (star (a (Fintype.equivFin Y y)) * a (Fintype.equivFin Y y')) := rfl
  have hunit : star (a (Fintype.equivFin Y y)) * a (Fintype.equivFin Y y') =
      Matrix.single y y' 1 := by
    show star (Matrix.single y0 ((Fintype.equivFin Y).symm (Fintype.equivFin Y y)) 1) *
        Matrix.single y0 ((Fintype.equivFin Y).symm (Fintype.equivFin Y y')) 1 = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_single, star_one, Matrix.single_mul_single_same, one_mul]
  rw [hl, hunit] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [CStarMatrix.star_apply]

/-- A linear map out of a matrix block, expanded along the matrix units. -/
theorem linearMap_eq_sum_single {A : Type*} [AddCommGroup A] [Module ℂ A]
    (Y : FiniteModel) (up : Matrix Y Y ℂ →ₗ[ℂ] A) (M : Matrix Y Y ℂ) :
    up M = ∑ y, ∑ y', M y y' • up (Matrix.single y y' 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single M]
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun y' _ ↦ ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Replacing both factors of `a⋆ b` by nearby elements. -/
theorem norm_star_mul_sub_star_mul_le {A : Type*} [NonUnitalCStarAlgebra A]
    (a a' b b' : A) {M η : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (ha' : ‖a' - a‖ ≤ η) (hb' : ‖b' - b‖ ≤ η) (hη1 : η ≤ 1) (hη0 : 0 ≤ η) :
    ‖star a' * b' - star a * b‖ ≤ (2 * M + 1) * η := by
  have e : star a' * b' - star a * b = star a' * (b' - b) + star (a' - a) * b := by
    rw [star_sub, mul_sub, sub_mul]
    abel
  rw [e]
  have ha'M : ‖a'‖ ≤ M + 1 := by
    have := norm_sub_norm_le a' a
    linarith
  have h1 : ‖star a' * (b' - b)‖ ≤ (M + 1) * η := by
    calc ‖star a' * (b' - b)‖ ≤ ‖star a'‖ * ‖b' - b‖ := norm_mul_le _ _
      _ = ‖a'‖ * ‖b' - b‖ := by rw [norm_star]
      _ ≤ (M + 1) * η :=
          mul_le_mul ha'M hb' (norm_nonneg _) (by linarith [(norm_nonneg a).trans ha])
  have h2 : ‖star (a' - a) * b‖ ≤ η * M := by
    calc ‖star (a' - a) * b‖ ≤ ‖star (a' - a)‖ * ‖b‖ := norm_mul_le _ _
      _ = ‖a' - a‖ * ‖b‖ := by rw [norm_star]
      _ ≤ η * M := mul_le_mul ha' hb (norm_nonneg _) hη0
  calc ‖star a' * (b' - b) + star (a' - a) * b‖
      ≤ ‖star a' * (b' - b)‖ + ‖star (a' - a) * b‖ := norm_add_le _ _
    _ ≤ (M + 1) * η + η * M := add_le_add h1 h2
    _ = (2 * M + 1) * η := by ring

end Maps

/-! ## The canonical trace on finite combinations of generators -/

section Trace

variable (G : Type u) [Group G]

/-- The canonical trace is norm contractive. -/
theorem norm_canonicalMaximalTrace_le (a : MaximalGroupCStar G) :
    ‖canonicalMaximalTrace G a‖ ≤ ‖a‖ := by
  rw [canonicalMaximalTrace_apply, canonicalCoefficientAtOne_eq_inner]
  calc ‖⟪deltaOne G, ((maximalGroupCStarToReduced G a : ReducedGroupCStar G) :
        GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)⟫_ℂ‖
      ≤ ‖deltaOne G‖ * ‖((maximalGroupCStarToReduced G a : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)‖ := norm_inner_le_norm _ _
    _ ≤ ‖deltaOne G‖ * (‖((maximalGroupCStarToReduced G a : ReducedGroupCStar G) :
          GroupHilbert G →L[ℂ] GroupHilbert G)‖ * ‖deltaOne G‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖maximalGroupCStarToReduced G a‖ := by
        rw [GroupVonNeumann.norm_deltaOne G, one_mul, mul_one]
        rfl
    _ ≤ ‖a‖ := NonUnitalStarAlgHom.norm_apply_le _ _

/-- **The pairing formula.**  For finite combinations of generators,
`τ(u_g⋆ (∑ c₁(s) u_s)⋆ (∑ c₂(t) u_t)) = ∑ₛ conj(c₁ s) c₂(s g)`, which is the
translation inner product of the reflected coefficient vectors. -/
theorem trace_star_gen_mul_star_mul (c₁ c₂ : G →₀ ℂ) (g : G) :
    canonicalMaximalTrace G (star (maximalGroupCStarGenerator G g) *
        (star (∑ s ∈ c₁.support, c₁ s • maximalGroupCStarGenerator G s) *
          ∑ t ∈ c₂.support, c₂ t • maximalGroupCStarGenerator G t)) =
      starInner (Finsupp.equivMapDomain (Equiv.inv G) c₁)
        (lTrans g (Finsupp.equivMapDomain (Equiv.inv G) c₂)) := by
  classical
  have hexp : star (maximalGroupCStarGenerator G g) *
      (star (∑ s ∈ c₁.support, c₁ s • maximalGroupCStarGenerator G s) *
        ∑ t ∈ c₂.support, c₂ t • maximalGroupCStarGenerator G t) =
      ∑ s ∈ c₁.support, ∑ t ∈ c₂.support,
        (star (c₁ s) * c₂ t) • maximalGroupCStarGenerator G (g⁻¹ * (s⁻¹ * t)) := by
    rw [star_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [star_smul, star_maximalGroupCStarGenerator, star_maximalGroupCStarGenerator,
      smul_mul_smul_comm, mul_smul_comm, maximalGroupCStarGenerator_mul,
      maximalGroupCStarGenerator_mul]
  have hcond : ∀ s t : G, g⁻¹ * (s⁻¹ * t) = 1 ↔ t = s * g := by
    intro s t
    constructor
    · intro h
      calc t = s * g * (g⁻¹ * (s⁻¹ * t)) := by group
        _ = s * g := by rw [h, mul_one]
    · intro h
      rw [h]
      group
  rw [hexp, map_sum]
  show _ = (Finsupp.equivMapDomain (Equiv.inv G) c₁).sum
    (fun x b ↦ (starRingEnd ℂ) b * (lTrans g (Finsupp.equivMapDomain (Equiv.inv G) c₂)) x)
  rw [Finsupp.sum_equivMapDomain, Finsupp.sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  dsimp only
  rw [map_sum]
  have hval : (lTrans g (Finsupp.equivMapDomain (Equiv.inv G) c₂)) ((Equiv.inv G) s) =
      c₂ (s * g) := by
    rw [lTrans_apply, Finsupp.equivMapDomain_apply]
    congr 1
    show (g⁻¹ * s⁻¹)⁻¹ = s * g
    rw [mul_inv_rev, inv_inv, inv_inv]
  rw [hval, Finset.sum_eq_single (s * g)]
  · rw [map_smul, canonicalMaximalTrace_generator, if_pos ((hcond s _).mpr rfl),
      smul_eq_mul, mul_one, starRingEnd_apply]
  · intro t _ hne
    rw [map_smul, canonicalMaximalTrace_generator,
      if_neg (fun h ↦ hne ((hcond s t).mp h)), smul_zero]
  · intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot, mul_zero, zero_smul, map_zero]

/-- The generators span a dense subspace, quantitatively. -/
theorem exists_finsupp_approx (x : MaximalGroupCStar G) {η : ℝ} (hη : 0 < η) :
    ∃ c : G →₀ ℂ,
      ‖(∑ s ∈ c.support, c s • maximalGroupCStarGenerator G s) - x‖ ≤ η := by
  have hx := maximalGroupCStar_dense_span_generator G x
  obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.mp hx η hη
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hb
  refine ⟨c, ?_⟩
  have hsum : (∑ s ∈ c.support, c s • maximalGroupCStarGenerator G s) = b := hc
  rw [hsum, norm_sub_rev, ← dist_eq_norm]
  exact hdist.le

end Trace

/-! ## Assembly -/

variable {G : Type u} [Group G]

/-- The correlation of the reflected coefficient vectors is the trace of the
approximate composite against `u_g⋆`. -/
theorem corr_eq_trace (Y : FiniteModel) (D : G → Matrix Y Y ℂ)
    (n : ℕ) (e : Y ≃ Fin n) (c : Fin n → Fin n → (G →₀ ℂ)) (g : G) :
    corr D (fun k y ↦ Finsupp.equivMapDomain (Equiv.inv G) (c k (e y))) g =
      canonicalMaximalTrace G (star (maximalGroupCStarGenerator G g) *
        ∑ y, ∑ y', D g y y' • ∑ k,
          star (∑ s ∈ (c k (e y)).support, c k (e y) s • maximalGroupCStarGenerator G s) *
            ∑ t ∈ (c k (e y')).support, c k (e y') t • maximalGroupCStarGenerator G t) := by
  rw [corr]
  dsimp only
  rw [Finset.mul_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Finset.mul_sum, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ ↦ ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, Finset.mul_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [trace_star_gen_mul_star_mul]

/-- **Lance's theorem at the maximal algebra**, invariant-mean form. -/
theorem hasInvariantMean_of_isNuclearCStarAlgebra_maximalGroupCStar
    (hnuc : IsNuclearCStarAlgebra (MaximalGroupCStar G)) :
    Amenability.HasInvariantMean G := by
  classical
  refine hasInvariantMean_of_almostInvariantVectors fun F ε hε ↦ ?_
  set δ : ℝ := min ε 1 / 16 with hδdef
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 16 := by
    have := min_le_right ε 1
    rw [hδdef]
    linarith
  let gen : G → MaximalGroupCStar G := maximalGroupCStarGenerator G
  let F' : Finset G := insert 1 (F ∪ F.image fun g ↦ g⁻¹)
  obtain ⟨Y, hY, down, up, hdownCP, hupCP, -, -, hrec⟩ :=
    exists_matrixModelApproximation_of_isNuclearCStarAlgebra hnuc (F'.image gen) δ hδpos
  letI : Nonempty Y := hY
  let D : G → Matrix Y Y ℂ := fun g ↦ down (gen g)
  have hD : PairPositive D :=
    pairPositive_of_isCompletelyPositive Y down hdownCP gen
      (star_maximalGroupCStarGenerator G) (maximalGroupCStarGenerator_mul G)
  obtain ⟨P, hP⟩ := exists_choi_factor Y up hupCP
  let n := Fintype.card Y
  let e : Y ≃ Fin n := Fintype.equivFin Y
  let M : ℝ := ∑ k, ∑ i, ‖P k i‖
  let K : ℝ := ∑ g ∈ F', ∑ y, ∑ y', ‖D g y y'‖
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hPM : ∀ k i, ‖P k i‖ ≤ M := fun k i ↦
    (Finset.single_le_sum (f := fun i ↦ ‖P k i‖) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun k ↦ ∑ i, ‖P k i‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ k))
  set L : ℝ := (K + 1) * ((n : ℝ) + 1) * (2 * M + 1) with hLdef
  have hLpos : 0 < L := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hL0 : L ≠ 0 := hLpos.ne'
  set η : ℝ := min 1 (δ / L) with hηdef
  have hηpos : 0 < η := lt_min one_pos (div_pos hδpos hLpos)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηL : L * η ≤ δ := by
    have hle : η ≤ δ / L := min_le_right _ _
    calc L * η ≤ L * (δ / L) := mul_le_mul_of_nonneg_left hle hLpos.le
      _ = δ := by field_simp
  have happrox : ∀ k i, ∃ c : G →₀ ℂ,
      ‖(∑ s ∈ c.support, c s • maximalGroupCStarGenerator G s) - P k i‖ ≤ η :=
    fun k i ↦ exists_finsupp_approx G (P k i) hηpos
  choose c hc using happrox
  let Q : Fin n → Fin n → MaximalGroupCStar G :=
    fun k i ↦ ∑ s ∈ (c k i).support, c k i s • maximalGroupCStarGenerator G s
  let d : Fin n → Y → (G →₀ ℂ) :=
    fun k y ↦ Finsupp.equivMapDomain (Equiv.inv G) (c k (e y))
  have hclose : ∀ g ∈ F', ‖corr D d g - 1‖ ≤ 2 * δ := by
    intro g hg
    have hθ : up (down (gen g)) =
        ∑ y, ∑ y', D g y y' • ∑ k, star (P k (e y)) * P k (e y') := by
      rw [linearMap_eq_sum_single Y up (down (gen g))]
      refine Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun y' _ ↦ ?_
      rw [hP]
    have hrec_g : ‖up (down (gen g)) - gen g‖ ≤ δ :=
      hrec (gen g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    have hterm : ∀ y y' : Y, ‖∑ k, star (Q k (e y)) * Q k (e y') -
        ∑ k, star (P k (e y)) * P k (e y')‖ ≤ (n : ℝ) * ((2 * M + 1) * η) := by
      intro y y'
      rw [← Finset.sum_sub_distrib]
      calc ‖∑ k, (star (Q k (e y)) * Q k (e y') - star (P k (e y)) * P k (e y'))‖
          ≤ ∑ k, ‖star (Q k (e y)) * Q k (e y') - star (P k (e y)) * P k (e y')‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k : Fin n, (2 * M + 1) * η :=
            Finset.sum_le_sum fun k _ ↦
              norm_star_mul_sub_star_mul_le _ _ _ _ (hPM k (e y)) (hPM k (e y'))
                (hc k (e y)) (hc k (e y')) hη1 hηpos.le
        _ = (n : ℝ) * ((2 * M + 1) * η) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hDK : ∑ y, ∑ y', ‖D g y y'‖ ≤ K :=
      Finset.single_le_sum (f := fun g ↦ ∑ y, ∑ y', ‖D g y y'‖)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hg
    have hθθ' : ‖(∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) -
        up (down (gen g))‖ ≤ δ := by
      rw [hθ, ← Finset.sum_sub_distrib]
      calc ‖∑ y, (∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y') -
            ∑ y', D g y y' • ∑ k, star (P k (e y)) * P k (e y'))‖
          = ‖∑ y, ∑ y', D g y y' • (∑ k, star (Q k (e y)) * Q k (e y') -
              ∑ k, star (P k (e y)) * P k (e y'))‖ := by
            congr 1
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun y' _ ↦ ?_
            rw [smul_sub]
        _ ≤ ∑ y, ∑ y', ‖D g y y'‖ * ((n : ℝ) * ((2 * M + 1) * η)) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y' _ ↦ ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_left (hterm y y') (norm_nonneg _)
        _ = (∑ y, ∑ y', ‖D g y y'‖) * ((n : ℝ) * ((2 * M + 1) * η)) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y _ ↦ ?_
            rw [Finset.sum_mul]
        _ ≤ K * ((n : ℝ) * ((2 * M + 1) * η)) :=
            mul_le_mul_of_nonneg_right hDK
              (mul_nonneg hn0 (mul_nonneg (by linarith) hηpos.le))
        _ = (K * n) * ((2 * M + 1) * η) := by ring
        _ ≤ ((K + 1) * ((n : ℝ) + 1)) * ((2 * M + 1) * η) :=
            mul_le_mul_of_nonneg_right (by nlinarith)
              (mul_nonneg (by linarith) hηpos.le)
        _ = L * η := by rw [hLdef]; ring
        _ ≤ δ := hηL
    have htr : corr D d g = canonicalMaximalTrace G (star (gen g) *
        ∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) :=
      corr_eq_trace Y D n e c g
    have hone : canonicalMaximalTrace G (star (gen g) * gen g) = 1 := by
      show canonicalMaximalTrace G (star (maximalGroupCStarGenerator G g) *
        maximalGroupCStarGenerator G g) = 1
      rw [star_maximalGroupCStarGenerator, maximalGroupCStarGenerator_mul, inv_mul_cancel]
      exact canonicalMaximalTrace_generator_one G
    rw [htr, ← hone, ← map_sub, ← mul_sub]
    calc ‖canonicalMaximalTrace G (star (gen g) *
          ((∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - gen g))‖
        ≤ ‖star (gen g) *
            ((∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - gen g)‖ :=
          norm_canonicalMaximalTrace_le G _
      _ ≤ ‖star (gen g)‖ *
            ‖(∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - gen g‖ :=
          norm_mul_le _ _
      _ = ‖(∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - gen g‖ := by
          rw [norm_star]
          show ‖maximalGroupCStarGenerator G g‖ * _ = _
          rw [norm_maximalGroupCStarGenerator, one_mul]
      _ ≤ ‖(∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - up (down (gen g))‖ +
            ‖up (down (gen g)) - gen g‖ := by
          have := norm_add_le
            ((∑ y, ∑ y', D g y y' • ∑ k, star (Q k (e y)) * Q k (e y')) - up (down (gen g)))
            (up (down (gen g)) - gen g)
          rwa [sub_add_sub_cancel] at this
      _ ≤ δ + δ := add_le_add hθθ' hrec_g
      _ = 2 * δ := by ring
  have h2δ : 2 * δ ≤ 1 / 4 := by linarith
  obtain ⟨ξ, hξ1, hξ⟩ := exists_almostInvariant_of_corr hD d F h2δ
    (hclose 1 (Finset.mem_insert_self _ _))
    fun g hg ↦ ⟨hclose g (Finset.mem_insert_of_mem (Finset.mem_union_left _ hg)),
      hclose g⁻¹ (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)))⟩
  refine ⟨ξ, hξ1, fun g hg ↦ (hξ g hg).trans ?_⟩
  have := min_le_left ε 1
  rw [hδdef]
  linarith

/-- **Lance's theorem at the maximal algebra.**  A discrete group whose maximal
group C⋆-algebra has the completely positive approximation property is
amenable. -/
theorem isAmenable_of_isNuclearCStarAlgebra_maximalGroupCStar
    (hnuc : IsNuclearCStarAlgebra (MaximalGroupCStar G)) :
    Amenability.IsAmenable G :=
  Amenability.isAmenable_of_hasInvariantMean
    (hasInvariantMean_of_isNuclearCStarAlgebra_maximalGroupCStar hnuc)

/-- The contrapositive, in the form a non-nuclearity sentence uses. -/
theorem not_isNuclearCStarAlgebra_maximalGroupCStar_of_not_isAmenable
    (hG : ¬ Amenability.IsAmenable G) :
    ¬ IsNuclearCStarAlgebra (MaximalGroupCStar G) :=
  fun hnuc ↦ hG (isAmenable_of_isNuclearCStarAlgebra_maximalGroupCStar hnuc)

end

end LanceMaximal
end GroupApproximation

open GroupApproximation.LanceMaximal

#audit_axioms GroupApproximation.LanceMaximal.pairPositive_of_isCompletelyPositive
#audit_axioms GroupApproximation.LanceMaximal.exists_choi_factor
#audit_axioms GroupApproximation.LanceMaximal.trace_star_gen_mul_star_mul
#audit_axioms GroupApproximation.LanceMaximal.hasInvariantMean_of_isNuclearCStarAlgebra_maximalGroupCStar
#audit_axioms GroupApproximation.LanceMaximal.isAmenable_of_isNuclearCStarAlgebra_maximalGroupCStar
#audit_axioms GroupApproximation.LanceMaximal.not_isNuclearCStarAlgebra_maximalGroupCStar_of_not_isAmenable
