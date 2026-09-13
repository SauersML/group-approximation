import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Data.Nat.Pairing
import GroupApproximation.Meta.AxiomGuard

/-!
# Integer polynomials bounded on a grid

A step toward "every countable subgroup of `GL_2` over a field has the Haagerup property"
(`non_mf_groups_exist.tex`, tex lines 1146--1147) in characteristic zero.

* (`finite_setOf_totalDegree_le_norm_eval_le`) Let `z_1, …, z_d : ℕ → ℂ` be injective.  For every
  `N` and every bound `C` on the grid `{0, …, N}^d`, only finitely many integer polynomials `P` of
  total degree at most `N` satisfy `‖P (z_1 (k_1), …, z_d (k_d))‖ ≤ C k` at every grid point `k`.
  The matrix of values of the monomials with exponents at most `N` at the grid points is invertible
  by the Combinatorial Nullstellensatz, so the coefficients of `P` are bounded.
* (`exists_grid_points`) There are such `z` for which evaluation at every grid point is injective
  on integer polynomials.  Take distinct members of a transcendence basis of `ℂ` over `ℤ`; the
  basis is infinite because `ℂ` is uncountable.
-/

namespace GroupApproximation
namespace IntegerGridFinite

open MvPolynomial
open scoped Matrix

variable {d : ℕ}

/-- The exponent vector `(e_1, …, e_d)`. -/
noncomputable def expo {N : ℕ} (e : Fin d → Fin (N + 1)) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (e i : ℕ)

theorem expo_apply {N : ℕ} (e : Fin d → Fin (N + 1)) (i : Fin d) : expo e i = e i := rfl

theorem expo_injective {N : ℕ} : Function.Injective (expo (d := d) (N := N)) :=
  fun _ _ h ↦ funext fun i ↦ Fin.ext (congrArg (fun m : Fin d →₀ ℕ ↦ m i) h)

/-- Every monomial of a polynomial of total degree at most `N` has exponents at most `N`. -/
theorem exists_expo_eq {R : Type*} [CommSemiring R] {N : ℕ} {P : MvPolynomial (Fin d) R}
    (hP : P.totalDegree ≤ N) {m : Fin d →₀ ℕ} (hm : m ∈ P.support) :
    ∃ e : Fin d → Fin (N + 1), expo e = m := by
  refine ⟨fun i ↦ ⟨m i, Nat.lt_succ_of_le ((monomial_le_degreeOf i hm).trans
    ((degreeOf_le_totalDegree P i).trans hP))⟩, ?_⟩
  ext i
  rfl

/-- Evaluation of a polynomial of total degree at most `N`, as a sum over exponent vectors. -/
theorem eval₂_eq_sum {N : ℕ} {P : MvPolynomial (Fin d) ℤ} (hP : P.totalDegree ≤ N)
    (x : Fin d → ℂ) :
    eval₂ (Int.castRingHom ℂ) x P =
      ∑ e : Fin d → Fin (N + 1), ((P.coeff (expo e) : ℤ) : ℂ) * ∏ i, x i ^ (e i : ℕ) := by
  classical
  have hsub : P.support ⊆ Finset.univ.image (expo (N := N)) := by
    intro m hm
    obtain ⟨e, he⟩ := exists_expo_eq hP hm
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, he⟩
  have h1 : ∑ m ∈ P.support, (Int.castRingHom ℂ) (P.coeff m) * ∏ i, x i ^ m i =
      ∑ m ∈ Finset.univ.image (expo (N := N)), (Int.castRingHom ℂ) (P.coeff m) * ∏ i, x i ^ m i :=
    Finset.sum_subset hsub fun m _ hm ↦ by rw [notMem_support_iff.mp hm, map_zero, zero_mul]
  have h2 : ∑ m ∈ Finset.univ.image (expo (N := N)),
      (Int.castRingHom ℂ) (P.coeff m) * ∏ i, x i ^ m i =
      ∑ e : Fin d → Fin (N + 1), ((P.coeff (expo e) : ℤ) : ℂ) * ∏ i, x i ^ (e i : ℕ) :=
    Finset.sum_image fun _ _ _ _ h ↦ expo_injective h
  exact (eval₂_eq' _ _ _).trans (h1.trans h2)

/-- The values of the monomials with exponents at most `N` at the grid points. -/
noncomputable def gridMatrix (z : Fin d → ℕ → ℂ) (N : ℕ) :
    Matrix (Fin d → Fin (N + 1)) (Fin d → Fin (N + 1)) ℂ :=
  Matrix.of fun k e ↦ ∏ i, z i (k i) ^ (e i : ℕ)

/-- **The grid matrix has trivial kernel** (Combinatorial Nullstellensatz). -/
theorem gridMatrix_mulVec_eq_zero {z : Fin d → ℕ → ℂ} (hz : ∀ i, Function.Injective (z i))
    {N : ℕ} {c : (Fin d → Fin (N + 1)) → ℂ} (hc : gridMatrix z N *ᵥ c = 0) : c = 0 := by
  classical
  have hP : (∑ e : Fin d → Fin (N + 1), monomial (expo e) (c e) : MvPolynomial (Fin d) ℂ) = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset _
      (fun i ↦ Finset.univ.image fun j : Fin (N + 1) ↦ z i j) (fun i ↦ ?_) (fun x hx ↦ ?_)
    · have hcard : (Finset.univ.image fun j : Fin (N + 1) ↦ z i j).card = N + 1 := by
        rw [Finset.card_image_of_injective _ fun a b h ↦ Fin.val_injective (hz i h),
          Finset.card_univ, Fintype.card_fin]
      refine lt_of_lt_of_eq ((degreeOf_lt_iff (Nat.succ_pos N)).mpr fun m hm ↦ ?_) hcard.symm
      obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp (support_sum hm)
      rw [Finset.mem_singleton.mp (support_monomial_subset he)]
      exact (e i).2
    · choose j hj using fun i ↦ Finset.mem_image.mp (hx i)
      have hxj : x = fun i ↦ z i (j i) := funext fun i ↦ (hj i).2.symm
      subst hxj
      have h := congrFun hc j
      rw [Pi.zero_apply] at h
      rw [← h, map_sum]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      rw [eval_monomial, Finsupp.prod_fintype]
      · exact mul_comm _ _
      · intro i
        exact pow_zero _
  funext e
  have h := congrArg (coeff (expo e)) hP
  rw [coeff_zero, coeff_sum, Finset.sum_eq_single e, coeff_monomial, if_pos rfl] at h
  · exact h
  · intro e' _ he'
    rw [coeff_monomial, if_neg fun h ↦ he' (expo_injective h)]
  · intro he
    exact absurd (Finset.mem_univ e) he

/-- **Integer polynomials bounded on a grid are finitely many.** -/
theorem finite_setOf_totalDegree_le_norm_eval_le (z : Fin d → ℕ → ℂ)
    (hz : ∀ i, Function.Injective (z i)) (N : ℕ) (C : (Fin d → Fin (N + 1)) → ℝ) :
    {P : MvPolynomial (Fin d) ℤ | P.totalDegree ≤ N ∧ ∀ k : Fin d → Fin (N + 1),
      ‖eval₂ (Int.castRingHom ℂ) (fun i ↦ z i (k i)) P‖ ≤ C k}.Finite := by
  classical
  have hA : IsUnit (gridMatrix z N) := Matrix.mulVec_injective_iff_isUnit.mp fun c c' h ↦
    sub_eq_zero.mp (gridMatrix_mulVec_eq_zero hz (by rw [Matrix.mulVec_sub, h, sub_self]))
  obtain ⟨u, hu⟩ := hA
  -- the coefficients are the inverse matrix applied to the values at the grid points
  have hc : ∀ P : MvPolynomial (Fin d) ℤ, P.totalDegree ≤ N → ∀ e,
      ((P.coeff (expo e) : ℤ) : ℂ) =
        ∑ k, (↑u⁻¹ : Matrix (Fin d → Fin (N + 1)) (Fin d → Fin (N + 1)) ℂ) e k *
          eval₂ (Int.castRingHom ℂ) (fun i ↦ z i (k i)) P := by
    intro P hP e
    have hw : (fun k : Fin d → Fin (N + 1) ↦ eval₂ (Int.castRingHom ℂ) (fun i ↦ z i (k i)) P) =
        gridMatrix z N *ᵥ fun e ↦ ((P.coeff (expo e) : ℤ) : ℂ) := by
      funext k
      rw [eval₂_eq_sum hP]
      simp only [Matrix.mulVec, dotProduct, gridMatrix, Matrix.of_apply]
      exact Finset.sum_congr rfl fun e _ ↦ mul_comm _ _
    have h1 : (fun e ↦ ((P.coeff (expo e) : ℤ) : ℂ)) =
        (↑u⁻¹ : Matrix (Fin d → Fin (N + 1)) (Fin d → Fin (N + 1)) ℂ) *ᵥ
          (gridMatrix z N *ᵥ fun e ↦ ((P.coeff (expo e) : ℤ) : ℂ)) := by
      rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
    have h2 := congrFun h1 e
    rw [← hw] at h2
    exact h2
  let R : (Fin d → Fin (N + 1)) → ℝ := fun e ↦
    ∑ k, ‖(↑u⁻¹ : Matrix (Fin d → Fin (N + 1)) (Fin d → Fin (N + 1)) ℂ) e k‖ * C k
  have hinj : Set.InjOn
      (fun (P : MvPolynomial (Fin d) ℤ) (e : Fin d → Fin (N + 1)) ↦ P.coeff (expo e))
      {P : MvPolynomial (Fin d) ℤ | P.totalDegree ≤ N ∧ ∀ k : Fin d → Fin (N + 1),
        ‖eval₂ (Int.castRingHom ℂ) (fun i ↦ z i (k i)) P‖ ≤ C k} := by
    intro P hP Q hQ h
    ext m
    by_cases hm : m ∈ P.support ∪ Q.support
    · obtain ⟨e, rfl⟩ : ∃ e : Fin d → Fin (N + 1), expo e = m := by
        rcases Finset.mem_union.mp hm with hm | hm
        · exact exists_expo_eq hP.1 hm
        · exact exists_expo_eq hQ.1 hm
      exact congrFun h e
    · rw [Finset.notMem_union] at hm
      rw [notMem_support_iff.mp hm.1, notMem_support_iff.mp hm.2]
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.pi (t := fun e ↦ Set.Icc (-⌈R e⌉) ⌈R e⌉)
    fun e ↦ Set.finite_Icc _ _).subset ?_
  rintro _ ⟨P, hP, rfl⟩
  refine Set.mem_univ_pi.mpr fun e ↦ Set.mem_Icc.mpr ?_
  show -⌈R e⌉ ≤ P.coeff (expo e) ∧ P.coeff (expo e) ≤ ⌈R e⌉
  have hle : ‖((P.coeff (expo e) : ℤ) : ℂ)‖ ≤ R e := by
    rw [hc P hP.1 e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hP.2 k) (norm_nonneg _)
  rw [Complex.norm_intCast] at hle
  have hceil := Int.le_ceil (R e)
  obtain ⟨h1, h2⟩ := abs_le.mp hle
  constructor
  · have h3 : (-(⌈R e⌉ : ℝ)) ≤ ((P.coeff (expo e) : ℤ) : ℝ) := by linarith
    exact_mod_cast h3
  · have h3 : ((P.coeff (expo e) : ℤ) : ℝ) ≤ (⌈R e⌉ : ℝ) := by linarith
    exact_mod_cast h3

/-- A sequence of complex numbers algebraically independent over `ℤ`. -/
theorem exists_algebraicIndependent_nat : ∃ y : ℕ → ℂ, AlgebraicIndependent ℤ y := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℤ ℂ
  have hinf : Infinite s := by
    by_contra hfin
    have : Finite s := not_infinite_iff_finite.mp hfin
    have hle := IsAlgClosed.cardinal_le_max_transcendence_basis' _ hs
    have : Countable ℂ := Cardinal.mk_le_aleph0_iff.mp
      (hle.trans (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
    exact not_countable_complex Set.countable_univ
  exact ⟨fun n ↦ (Infinite.natEmbedding s n : ℂ), hs.1.comp _ (Infinite.natEmbedding s).injective⟩

/-- **Grid points with injective evaluation.** -/
theorem exists_grid_points (d : ℕ) :
    ∃ z : Fin d → ℕ → ℂ, (∀ i, Function.Injective (z i)) ∧
      ∀ k : Fin d → ℕ, Function.Injective (eval₂Hom (Int.castRingHom ℂ) fun i ↦ z i (k i)) := by
  obtain ⟨y, hy⟩ := exists_algebraicIndependent_nat
  refine ⟨fun i j ↦ y (Nat.pair (i : ℕ) j),
    fun i _ _ h ↦ (Nat.pair_eq_pair.mp (hy.injective h)).2, fun k ↦ ?_⟩
  have hk : AlgebraicIndependent ℤ fun i : Fin d ↦ y (Nat.pair (i : ℕ) (k i)) :=
    hy.comp (fun i : Fin d ↦ Nat.pair (i : ℕ) (k i)) fun _ _ h ↦ Fin.ext (Nat.pair_eq_pair.mp h).1
  rw [algebraicIndependent_iff_injective_aeval] at hk
  refine fun P Q h ↦ hk ?_
  change eval₂ (algebraMap ℤ ℂ) _ P = eval₂ (algebraMap ℤ ℂ) _ Q
  rw [RingHom.eq_intCast' (algebraMap ℤ ℂ)]
  exact h

end IntegerGridFinite
end GroupApproximation

#audit_axioms GroupApproximation.IntegerGridFinite.expo_injective
#audit_axioms GroupApproximation.IntegerGridFinite.exists_expo_eq
#audit_axioms GroupApproximation.IntegerGridFinite.eval₂_eq_sum
#audit_axioms GroupApproximation.IntegerGridFinite.gridMatrix_mulVec_eq_zero
#audit_axioms GroupApproximation.IntegerGridFinite.finite_setOf_totalDegree_le_norm_eval_le
#audit_axioms GroupApproximation.IntegerGridFinite.exists_algebraicIndependent_nat
#audit_axioms GroupApproximation.IntegerGridFinite.exists_grid_points
