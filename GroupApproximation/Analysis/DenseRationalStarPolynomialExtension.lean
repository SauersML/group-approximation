import GroupApproximation.Analysis.RationalNoncommutativeStarPolynomial

/-!
# Extending rational polynomial norm data from a dense sequence

This module isolates the completion step in the reduced-product diagonal
argument.  A countable family `a_i` is equipped with explicit sequential
approximants for every point of `A`.  If a family `b_i` in a complete target
has the same norms on every rational noncommutative star polynomial, the
approximating `b_i` sequences have unique limits.  Those limits preserve the
metric and all star-ring operations.

The separate scalar-extension tail upgrades rational-complex homogeneity to
complex homogeneity using density of `Q(i)` in `C`.
-/

namespace GroupApproximation
namespace DenseRationalStarPolynomialExtension

open Filter
open RationalNoncommutativeStarPolynomial

noncomputable section

universe u v

/-- Explicit sequential density data for a countable family. -/
structure ApproximationScheme (A : Type u) [PseudoMetricSpace A]
    (a : ℕ → A) where
  index : A → ℕ → ℕ
  tendsto_index : ∀ x, Tendsto (fun n ↦ a (index x n)) atTop (nhds x)

private theorem exists_dense_index {A : Type u} [MetricSpace A]
    (a : ℕ → A) (ha : DenseRange a) (x : A) (n : ℕ) :
    ∃ j, dist (a j) x < (1 : ℝ) / (n + 1) := by
  have hx : x ∈ closure (Set.range a) := by
    rw [ha.closure_range]
    exact Set.mem_univ x
  rw [Metric.mem_closure_iff] at hx
  obtain ⟨y, ⟨j, rfl⟩, hy⟩ := hx ((1 : ℝ) / (n + 1)) (by positivity)
  exact ⟨j, by simpa [dist_comm] using hy⟩

/-- Every dense sequence has explicit sequential approximation data. -/
def ApproximationScheme.ofDenseRange {A : Type u} [MetricSpace A]
    (a : ℕ → A) (ha : DenseRange a) : ApproximationScheme A a where
  index x n := Classical.choose (exists_dense_index a ha x n)
  tendsto_index x := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have herr := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε := by
      have := (Metric.tendsto_nhds.mp herr) ε hε
      filter_upwards [this] with n hn
      simpa only [Real.dist_eq, sub_zero, Nat.cast_add, Nat.cast_one,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))] using hn
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
    refine ⟨N, fun n hn ↦ ?_⟩
    exact (Classical.choose_spec (exists_dense_index a ha x n)).trans (hN n hn)

variable {A : Type u} {D : Type v} [CStarAlgebra A] [CStarAlgebra D]
variable (a : ℕ → A) (b : ℕ → D)
variable (S : ApproximationScheme A a)
variable (hnorm : ∀ p : Polynomial, ‖eval b p‖ = ‖eval a p‖)
include hnorm

private theorem dist_generators (r s : ℕ) : dist (b r) (b s) = dist (a r) (a s) := by
  rw [dist_eq_norm, dist_eq_norm]
  simpa using hnorm (sub (.generator r) (.generator s))

private theorem cauchy_bApprox (x : A) :
    CauchySeq (fun n ↦ b (S.index x n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsrc := (Metric.tendsto_atTop.1 (S.tendsto_index x)) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := hsrc
  refine ⟨N, fun m hm n hn ↦ ?_⟩
  rw [dist_generators a b hnorm]
  have hxn : dist x (a (S.index x n)) < ε / 2 := by
    rw [dist_comm]
    exact hN n hn
  exact (dist_triangle _ x _).trans_lt (by linarith [hN m hm, hxn])

/-- The unique target limit associated to `x`. -/
def extension (x : A) : D :=
  Classical.choose (cauchySeq_tendsto_of_complete (cauchy_bApprox a b S hnorm x))

theorem tendsto_extension (x : A) :
    Tendsto (fun n ↦ b (S.index x n)) atTop
      (nhds (extension a b S hnorm x)) :=
  Classical.choose_spec
    (cauchySeq_tendsto_of_complete (cauchy_bApprox a b S hnorm x))

omit hnorm in
private theorem eq_of_parallel_limits
    {u v : ℕ → D} {u' v' : ℕ → A} {x y : D} {x' : A}
    (hu : Tendsto u atTop (nhds x)) (hv : Tendsto v atTop (nhds y))
    (hu' : Tendsto u' atTop (nhds x')) (hv' : Tendsto v' atTop (nhds x'))
    (heq : ∀ n, ‖u n - v n‖ = ‖u' n - v' n‖) : x = y := by
  have ht : Tendsto (fun n ↦ ‖u n - v n‖) atTop (nhds ‖x - y‖) :=
    (hu.sub hv).norm
  have hs : Tendsto (fun n ↦ ‖u' n - v' n‖) atTop (nhds 0) := by
    simpa using (hu'.sub hv').norm
  have hs' : Tendsto (fun n ↦ ‖u n - v n‖) atTop (nhds 0) :=
    (tendsto_congr' (Eventually.of_forall heq)).mpr hs
  have hzero : ‖x - y‖ = 0 := tendsto_nhds_unique ht hs'
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem extension_zero : extension a b S hnorm 0 = 0 := by
  apply eq_of_parallel_limits
    (tendsto_extension a b S hnorm 0) tendsto_const_nhds
    (S.tendsto_index 0) tendsto_const_nhds
  intro n
  simpa using hnorm (.generator (S.index 0 n))

theorem extension_add (x y : A) :
    extension a b S hnorm (x + y) =
      extension a b S hnorm x + extension a b S hnorm y := by
  apply eq_of_parallel_limits
    (tendsto_extension a b S hnorm (x + y))
    ((tendsto_extension a b S hnorm x).add
      (tendsto_extension a b S hnorm y))
    (S.tendsto_index (x + y))
    ((S.tendsto_index x).add (S.tendsto_index y))
  intro n
  simpa using hnorm
    (sub (.generator (S.index (x + y) n))
      (.add (.generator (S.index x n)) (.generator (S.index y n))))

theorem extension_mul (x y : A) :
    extension a b S hnorm (x * y) =
      extension a b S hnorm x * extension a b S hnorm y := by
  apply eq_of_parallel_limits
    (tendsto_extension a b S hnorm (x * y))
    ((tendsto_extension a b S hnorm x).mul
      (tendsto_extension a b S hnorm y))
    (S.tendsto_index (x * y))
    ((S.tendsto_index x).mul (S.tendsto_index y))
  intro n
  simpa using hnorm
    (sub (.generator (S.index (x * y) n))
      (.mul (.generator (S.index x n)) (.generator (S.index y n))))

theorem extension_star (x : A) :
    extension a b S hnorm (star x) = star (extension a b S hnorm x) := by
  apply eq_of_parallel_limits
    (tendsto_extension a b S hnorm (star x))
    (continuous_star.continuousAt.tendsto.comp
      (tendsto_extension a b S hnorm x))
    (S.tendsto_index (star x))
    (continuous_star.continuousAt.tendsto.comp (S.tendsto_index x))
  intro n
  simpa using hnorm
    (sub (.generator (S.index (star x) n))
      (.star (.generator (S.index x n))))

theorem extension_rat_smul (q : ℚ × ℚ) (x : A) :
    extension a b S hnorm (RationalHermitian.ofRatPair q • x) =
      RationalHermitian.ofRatPair q • extension a b S hnorm x := by
  apply eq_of_parallel_limits
    (tendsto_extension a b S hnorm (RationalHermitian.ofRatPair q • x))
    ((tendsto_extension a b S hnorm x).const_smul
      (RationalHermitian.ofRatPair q))
    (S.tendsto_index (RationalHermitian.ofRatPair q • x))
    ((S.tendsto_index x).const_smul (RationalHermitian.ofRatPair q))
  intro n
  simpa using hnorm
    (sub (.generator (S.index (RationalHermitian.ofRatPair q • x) n))
      (.smul q (.generator (S.index x n))))

theorem extension_dist (x y : A) :
    dist (extension a b S hnorm x) (extension a b S hnorm y) = dist x y := by
  have ht : Tendsto
      (fun n ↦ dist (b (S.index x n)) (b (S.index y n))) atTop
      (nhds (dist (extension a b S hnorm x) (extension a b S hnorm y))) :=
    (tendsto_extension a b S hnorm x).dist
      (tendsto_extension a b S hnorm y)
  have hs : Tendsto
      (fun n ↦ dist (a (S.index x n)) (a (S.index y n))) atTop
      (nhds (dist x y)) :=
    (S.tendsto_index x).dist (S.tendsto_index y)
  have ht' : Tendsto
      (fun n ↦ dist (b (S.index x n)) (b (S.index y n))) atTop
      (nhds (dist x y)) := by
    apply (tendsto_congr' ?_).mpr hs
    exact Eventually.of_forall fun n ↦ dist_generators a b hnorm _ _
  exact tendsto_nhds_unique ht ht'

theorem extension_isometry : Isometry (extension a b S hnorm) :=
  fun x y ↦ by
    simpa [edist_dist] using extension_dist a b S hnorm x y

private def scalarApproximation (c : ℂ) (n : ℕ) : ℚ × ℚ :=
  Classical.choose (RationalHermitian.exists_rat_pair_close c
    (by positivity : (0 : ℝ) < 1 / (n + 1)))

omit hnorm in
private theorem scalarApproximation_close (c : ℂ) (n : ℕ) :
    ‖c - RationalHermitian.ofRatPair (scalarApproximation c n)‖ <
      (1 : ℝ) / (n + 1) :=
  Classical.choose_spec (RationalHermitian.exists_rat_pair_close c
    (by positivity : (0 : ℝ) < 1 / (n + 1)))

omit hnorm in
private theorem tendsto_scalarApproximation (c : ℂ) :
    Tendsto (fun n ↦ RationalHermitian.ofRatPair (scalarApproximation c n))
      atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have herr := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε := by
    have := (Metric.tendsto_nhds.mp herr) ε hε
    filter_upwards [this] with n hn
    simpa only [Real.dist_eq, sub_zero, Nat.cast_add, Nat.cast_one,
      abs_of_pos (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact (scalarApproximation_close c n).trans (hN n hn)

theorem extension_smul (c : ℂ) (x : A) :
    extension a b S hnorm (c • x) = c • extension a b S hnorm x := by
  let q : ℕ → ℚ × ℚ := scalarApproximation c
  have hq : Tendsto (fun n ↦ RationalHermitian.ofRatPair (q n))
      atTop (nhds c) := tendsto_scalarApproximation c
  have hx : Tendsto (fun n ↦ RationalHermitian.ofRatPair (q n) • x)
      atTop (nhds (c • x)) := hq.smul tendsto_const_nhds
  have hleft : Tendsto
      (fun n ↦ extension a b S hnorm
        (RationalHermitian.ofRatPair (q n) • x)) atTop
      (nhds (extension a b S hnorm (c • x))) :=
    (extension_isometry a b S hnorm).continuous.tendsto _ |>.comp hx
  have hright : Tendsto
      (fun n ↦ RationalHermitian.ofRatPair (q n) • extension a b S hnorm x)
      atTop (nhds (c • extension a b S hnorm x)) :=
    hq.smul tendsto_const_nhds
  have heq : (fun n ↦ extension a b S hnorm
      (RationalHermitian.ofRatPair (q n) • x)) =
      fun n ↦ RationalHermitian.ofRatPair (q n) • extension a b S hnorm x := by
    funext n
    exact extension_rat_smul a b S hnorm (q n) x
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The isometric nonunital star homomorphism forced by rational polynomial
norm agreement on a sequentially dense family. -/
def extensionHom : A →⋆ₙₐ[ℂ] D where
  toFun := extension a b S hnorm
  map_zero' := extension_zero a b S hnorm
  map_add' := extension_add a b S hnorm
  map_mul' := extension_mul a b S hnorm
  map_smul' := extension_smul a b S hnorm
  map_star' := extension_star a b S hnorm

theorem extensionHom_injective : Function.Injective (extensionHom a b S hnorm) :=
  (extension_isometry a b S hnorm).injective

end

end DenseRationalStarPolynomialExtension
end GroupApproximation
