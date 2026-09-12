import GroupApproximation.KOne.AryShapeCalculus
import GroupApproximation.Meta.AxiomGuard

/-!
# Rank certificates for cylinder-sum idempotents, at arbitrary arity

`KOne/CylinderCornerRank.lean` over a complete matrix family on an alphabet `ι`.  A
depth-`n` cylinder sum `f = Σ_{γ ∈ T} p_γ` is represented at every interface `ℓ ≥ n` by a
matrix whose rank is exactly `|T|·|ι|^{ℓ-n}`: compressing between the words extending `T`
exhibits an identity matrix of that size (lower bound), while `p_γ = s_γ·t_γ` bounds the
rank of each summand by the width of the middle interface (upper bound).
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- Concatenation of function-words. -/
def appendFun {n r ℓ : ℕ} (h : n + r = ℓ) (γ : Fin n → ι) (δ : Fin r → ι) : Fin ℓ → ι :=
  fun i ↦ if hi : (i : ℕ) < n then γ ⟨i, hi⟩ else δ ⟨(i : ℕ) - n, by omega⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ofFn_appendFun {n r ℓ : ℕ} (h : n + r = ℓ) (γ : Fin n → ι) (δ : Fin r → ι) :
    List.ofFn (appendFun h γ δ) = List.ofFn γ ++ List.ofFn δ := by
  apply List.ext_getElem
  · simp [List.length_ofFn, List.length_append]
    omega
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    rw [List.getElem_append]
    by_cases hi : i < n
    · rw [dif_pos (by simpa [List.length_ofFn] using hi)]
      simp [appendFun, hi]
    · rw [dif_neg (by simpa [List.length_ofFn] using hi)]
      simp [appendFun, hi, List.length_ofFn]

/-- The core compression computation: conjugating a cylinder sum by concatenated words
produces Kronecker deltas. -/
theorem wordT_cylSum_wordS {n : ℕ} (T : Finset (Fin n → ι)) {r : ℕ}
    (γ γ' : Fin n → ι) (δ δ' : Fin r → ι) :
    F.wordT (List.ofFn γ ++ List.ofFn δ) * (∑ α ∈ T, F.cylinder (List.ofFn α)) *
      F.wordS (List.ofFn γ' ++ List.ofFn δ') =
    if γ = γ' ∧ δ = δ' ∧ γ ∈ T then 1 else 0 := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul]
  have hterm : ∀ α ∈ T,
      F.wordT (List.ofFn γ ++ List.ofFn δ) * F.cylinder (List.ofFn α) *
        F.wordS (List.ofFn γ' ++ List.ofFn δ') =
      if α = γ ∧ γ = γ' ∧ δ = δ' then 1 else 0 := by
    intro α _
    rw [F.wordT_append, F.wordS_append, cylinder]
    rw [show F.wordT (List.ofFn δ) * F.wordT (List.ofFn γ) *
        (F.wordS (List.ofFn α) * F.wordT (List.ofFn α)) *
        (F.wordS (List.ofFn γ') * F.wordS (List.ofFn δ')) =
      F.wordT (List.ofFn δ) *
        ((F.wordT (List.ofFn γ) * F.wordS (List.ofFn α)) *
          (F.wordT (List.ofFn α) * F.wordS (List.ofFn γ'))) *
        F.wordS (List.ofFn δ') from by noncomm_ring,
      F.powerFamily_orthogonal n γ α, F.powerFamily_orthogonal n α γ']
    by_cases h1 : γ = α
    · by_cases h2 : α = γ'
      · rw [if_pos h1, if_pos h2, one_mul, mul_one, F.powerFamily_orthogonal r δ δ']
        by_cases h3 : δ = δ'
        · rw [if_pos h3, if_pos ⟨h1.symm, h1.trans h2, h3⟩]
        · rw [if_neg h3, if_neg (fun hc ↦ h3 hc.2.2)]
      · rw [if_pos h1, if_neg h2,
          show F.wordT (List.ofFn δ) * ((1 : A) * 0) * F.wordS (List.ofFn δ') = 0 from by
            noncomm_ring,
          if_neg (fun hc ↦ h2 (hc.1.trans hc.2.1))]
    · rw [if_neg h1,
        show F.wordT (List.ofFn δ) * ((0 : A) * (if α = γ' then (1 : A) else 0)) *
          F.wordS (List.ofFn δ') = 0 from by noncomm_ring,
        if_neg (fun hc ↦ h1 hc.1.symm)]
  rw [Finset.sum_congr rfl hterm]
  by_cases hγT : γ ∈ T
  · rw [Finset.sum_eq_single γ]
    · by_cases h2 : γ = γ' ∧ δ = δ'
      · rw [if_pos ⟨rfl, h2.1, h2.2⟩, if_pos ⟨h2.1, h2.2, hγT⟩]
      · rw [if_neg (by tauto), if_neg (by tauto)]
    · intro α _ hα
      rw [if_neg (by tauto)]
    · intro hγ
      exact absurd hγT hγ
  · rw [if_neg (by tauto)]
    refine Finset.sum_eq_zero fun α hα ↦ ?_
    rw [if_neg ?_]
    rintro ⟨rfl, -, -⟩
    exact hγT hα

variable {k : Type*} [Field k] [Algebra k A]

/-- Cylinder sums lie in every square shape span at depth `≥ n`. -/
theorem cylSum_mem_shapeSpan {n : ℕ} (T : Finset (Fin n → ι)) {m : ℕ} (hm : n ≤ m) :
    (∑ γ ∈ T, F.cylinder (List.ofFn γ)) ∈ Submodule.span k (F.shapeMonomials m m) := by
  refine Submodule.sum_mem _ fun γ _ ↦ ?_
  have h := F.monomial_mem_shapeSpan (k := k) (List.ofFn γ) (List.ofFn γ) (m - n)
  have hlen : (List.ofFn γ).length + (m - n) = m := by
    simp only [List.length_ofFn]
    omega
  rw [hlen] at h
  exact h

/-- **Lower rank certificate**: any matrix representing the cylinder sum at interface
`ℓ` has rank at least `|T|·|ι|^{ℓ-n}`. -/
theorem card_le_rank_of_shapeRep_cylSum [Nontrivial A] {n ℓ : ℕ}
    (T : Finset (Fin n → ι)) (hℓ : n ≤ ℓ) {M : Matrix (Fin ℓ → ι) (Fin ℓ → ι) k}
    (hM : F.ShapeRep ℓ ℓ M (∑ γ ∈ T, F.cylinder (List.ofFn γ))) :
    T.card * Fintype.card ι ^ (ℓ - n) ≤ M.rank := by
  classical
  set ρ : Type _ := {γ // γ ∈ T} × (Fin (ℓ - n) → ι) with hρ
  have hsum : n + (ℓ - n) = ℓ := by omega
  set wf : ρ → (Fin ℓ → ι) := fun p ↦ appendFun hsum p.1.1 p.2 with hwf
  have hentry : ∀ p p' : ρ, M (wf p) (wf p') = if p = p' then 1 else 0 := by
    intro p p'
    apply (algebraMap k A).injective
    rw [← F.shapeRep_entry hM (wf p) (wf p')]
    simp only [hwf]
    rw [ofFn_appendFun, ofFn_appendFun, F.wordT_cylSum_wordS T p.1.1 p'.1.1 p.2 p'.2]
    by_cases hp : p = p'
    · rw [if_pos hp, if_pos (by refine ⟨?_, ?_, p.1.2⟩ <;> rw [hp]), map_one]
    · rw [if_neg hp, if_neg ?_, map_zero]
      rintro ⟨h1, h2, -⟩
      exact hp (Prod.ext (Subtype.ext h1) h2)
  set U : Matrix ρ (Fin ℓ → ι) k := Matrix.of fun p w ↦ if w = wf p then 1 else 0 with hU
  set V : Matrix (Fin ℓ → ι) ρ k := Matrix.of fun w p ↦ if w = wf p then 1 else 0 with hV
  have hUMV : U * M * V = 1 := by
    ext p p'
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (wf p')]
    · rw [Matrix.mul_apply, Finset.sum_eq_single (wf p)]
      · rw [hU, hV]
        simp [hentry p p', Matrix.one_apply]
      · intro w _ hw
        rw [hU]
        simp only [Matrix.of_apply, if_neg hw]
        rw [zero_mul]
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
    · intro w _ hw
      rw [hV]
      simp only [Matrix.of_apply, if_neg hw]
      rw [mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  have hcard : Fintype.card ρ = T.card * Fintype.card ι ^ (ℓ - n) := by
    show Fintype.card ({γ // γ ∈ T} × (Fin (ℓ - n) → ι)) = _
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin]
  calc (T.card * Fintype.card ι ^ (ℓ - n) : ℕ)
      = Fintype.card ρ := hcard.symm
    _ = (1 : Matrix ρ ρ k).rank := (Matrix.rank_one).symm
    _ = (U * M * V).rank := by rw [hUMV]
    _ ≤ (U * M).rank := Matrix.rank_mul_le_left _ _
    _ ≤ M.rank := Matrix.rank_mul_le_right _ _

/-- **Upper rank certificate**: any matrix representing the cylinder sum at interface
`m` has rank at most `|T|·|ι|^{m-n}`. -/
theorem rank_le_card_of_shapeRep_cylSum [Nontrivial A] {n m : ℕ}
    (T : Finset (Fin n → ι)) (hm : n ≤ m) {M : Matrix (Fin m → ι) (Fin m → ι) k}
    (hM : F.ShapeRep m m M (∑ γ ∈ T, F.cylinder (List.ofFn γ))) :
    M.rank ≤ T.card * Fintype.card ι ^ (m - n) := by
  classical
  have hfac : ∀ γ : Fin n → ι, ∃
      (P : Matrix (Fin m → ι) (Fin (m - n) → ι) k)
      (Q : Matrix (Fin (m - n) → ι) (Fin m → ι) k),
      F.ShapeRep m m (P * Q) (F.cylinder (List.ofFn γ)) := by
    intro γ
    have hlen : (List.ofFn γ).length + (m - n) = m := by
      simp only [List.length_ofFn]
      omega
    have hs : F.wordS (List.ofFn γ) ∈ Submodule.span k (F.shapeMonomials m (m - n)) := by
      have h := F.monomial_mem_shapeSpan (k := k) (List.ofFn γ) [] (m - n)
      rw [show F.wordS (List.ofFn γ) * F.wordT [] = F.wordS (List.ofFn γ) from by simp,
        hlen, show ([] : List ι).length + (m - n) = m - n from by simp] at h
      exact h
    have ht : F.wordT (List.ofFn γ) ∈ Submodule.span k (F.shapeMonomials (m - n) m) := by
      have h := F.monomial_mem_shapeSpan (k := k) [] (List.ofFn γ) (m - n)
      rw [show F.wordS [] * F.wordT (List.ofFn γ) = F.wordT (List.ofFn γ) from by simp,
        hlen, show ([] : List ι).length + (m - n) = m - n from by simp] at h
      exact h
    obtain ⟨P, hP⟩ := F.exists_shapeRep hs
    obtain ⟨Q, hQ⟩ := F.exists_shapeRep ht
    exact ⟨P, Q, by rw [cylinder]; exact F.shapeRep_mul hP hQ⟩
  choose P Q hPQ using hfac
  have hsumrep : F.ShapeRep m m (∑ γ ∈ T, P γ * Q γ)
      (∑ γ ∈ T, F.cylinder (List.ofFn γ)) :=
    F.shapeRep_finsetSum T _ _ fun γ _ ↦ hPQ γ
  have hMe : M = ∑ γ ∈ T, P γ * Q γ :=
    F.shapeRep_unique (algebraMap k A).injective hM hsumrep
  rw [hMe]
  calc (∑ γ ∈ T, P γ * Q γ).rank
      ≤ ∑ γ ∈ T, (P γ * Q γ).rank := rank_finsetSum_le T _
    _ ≤ ∑ _γ ∈ T, Fintype.card ι ^ (m - n) := by
        refine Finset.sum_le_sum fun γ _ ↦ ?_
        calc (P γ * Q γ).rank ≤ (P γ).rank := Matrix.rank_mul_le_left _ _
          _ ≤ Fintype.card (Fin (m - n) → ι) := Matrix.rank_le_card_width _
          _ = Fintype.card ι ^ (m - n) := by rw [Fintype.card_fun, Fintype.card_fin]
    _ = T.card * Fintype.card ι ^ (m - n) := by
        rw [Finset.sum_const, smul_eq_mul]

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.ofFn_appendFun
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_cylSum_wordS
#audit_axioms GroupApproximation.CompleteMatrixFamily.card_le_rank_of_shapeRep_cylSum
#audit_axioms GroupApproximation.CompleteMatrixFamily.rank_le_card_of_shapeRep_cylSum
