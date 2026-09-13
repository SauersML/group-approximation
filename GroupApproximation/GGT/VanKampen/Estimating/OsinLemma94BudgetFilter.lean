import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94Pieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the side budget over the polygons with an (A1) side

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`.  Assume that `S ≥ n √ρ`.  Then `S_i ≥ n_i √ρ / 60` for
some `i`."  A component with no arc of type (A1) has `S_i = 0`.  It adds nothing to the density
`∑ S_i ≥ n √ρ`, so the metric half does not need its sides in the side budget.

The side budget sums `k_i` only over the polygons with an (A1) side.  Value-one bubbles on a
spur tree give arbitrarily many polygons with no (A1) side while `n = 1`.  This module
reindexes the metric half, `OsinLemma94DensePolygonsAntiparallel`, over any set of polygons
that contains every polygon with a side in the class `A`.

* `classWordLength_eq_zero_of_forall_not_mem`: a polygon with no side in `A` has `S_k = 0`.
* `OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on`: the metric half, with the side
  budget summed over such a set of polygons.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **A polygon with no side in `A` has `S_k = 0`.** -/
theorem classWordLength_eq_zero_of_forall_not_mem {G : Type u} [Group G] {Lambda : Type w}
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A : Set ℕ) (h : ∀ i < n, i ∉ A) :
    classWordLength word n A = 0 := by
  classical
  unfold classWordLength
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [if_neg (h i (Finset.mem_range.mp hi))]

/-- **The metric half, with the side budget over the polygons with a side in `A`.**
`OsinLemma94DensePolygonsAntiparallel` budgets the sides of all `d` polygons.  Here the budget
runs over a set `s` of polygons that contains every polygon with a side in `A` (Osin's class
`N1`).  The other polygons have `S_k = 0`, so the metric half applies to the polygons of `s`
alone, and a backwards connector pair on one of them is a pair on an original polygon. -/
theorem OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on {G : Type u} [Group G]
    {Lambda : Type w} {D : RelGenSet G Lambda} {lambda c : ℝ} {eps rho K : ℕ}
    (hmetric : OsinLemma94DensePolygonsAntiparallel D lambda c eps rho K)
    {n d : ℕ} (hn : 0 < n) (sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
    (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ) (s : Finset (Fin d))
    (hs : ∀ k, ∀ i < sideCount k, i ∈ A k → k ∈ s)
    (hbudget : (∑ k ∈ s, sideCount k) ≤ K * n)
    (hclosed : ∀ k, v k (sideCount k) = v k 0)
    (hstep : ∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i))
    (hqg : ∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
      IsLambdaCQuasiGeodesicWord D lambda c (word k i))
    (hshort : ∀ k i, i < sideCount k → i ∉ B k →
      HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ eps)
    (hdense : (n : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k)) :
    ∃ k : Fin d, ∃ C : WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) eps,
      C.b' < C.b := by
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  have hreindex : ∀ {M : Type} [AddCommMonoid M] (f : Fin d → M),
      ∑ k' : Fin (Fintype.card s), f (e k').1 = ∑ k ∈ s, f k := by
    intro M _ f
    exact (Fintype.sum_equiv e (fun k' => f (e k').1) (fun x : s => f x.1) fun _ => rfl).trans
      (Finset.sum_coe_sort _ _)
  have hbudget' : (∑ k' : Fin (Fintype.card s), sideCount (e k').1) ≤ K * n :=
    (hreindex sideCount).trans_le hbudget
  have hzero : ∑ k ∈ s, classWordLength (word k) (sideCount k) (A k) =
      ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) :=
    Finset.sum_subset (Finset.subset_univ s) fun k _ hk =>
      classWordLength_eq_zero_of_forall_not_mem (word k) (sideCount k) (A k)
        fun i hi hiA => hk (hs k i hi hiA)
  have hdense' : (n : ℝ) * Real.sqrt (rho : ℝ) ≤
      ∑ k' : Fin (Fintype.card s),
        classWordLength (word (e k').1) (sideCount (e k').1) (A (e k').1) :=
    hdense.trans_eq ((hreindex fun k => classWordLength (word k) (sideCount k) (A k)).trans
      hzero).symm
  obtain ⟨k', C, hback⟩ := hmetric n (Fintype.card s) hn (fun k' => sideCount (e k').1)
    (fun k' => v (e k').1) (fun k' => word (e k').1) (fun k' => A (e k').1)
    (fun k' => B (e k').1) hbudget' (fun k' => hclosed (e k').1)
    (fun k' i hi => hstep (e k').1 i hi) (fun k' i hi hmem => hqg (e k').1 i hi hmem)
    (fun k' i hi hnot => hshort (e k').1 i hi hnot) hdense'
  exact ⟨(e k').1, C, hback⟩

#audit_axioms GroupApproximation.GGT.VanKampen.classWordLength_eq_zero_of_forall_not_mem
#audit_axioms
  GroupApproximation.GGT.VanKampen.OsinLemma94DensePolygonsAntiparallel.exists_of_budget_on

end GroupApproximation.GGT.VanKampen
