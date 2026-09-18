import GroupApproximation.Manuscript.NonMFNotes.Full.RCFDecision.Encoding.Evals

/-!
# The quantifier-free matrix of `Φ(P, n, c)`

`non_mf_group_notes.tex`, `prop:mf-upper-bound`, printed sentence `9eae4d68673a`.
At an assignment `ρ`, the matrix of `encFormula P n d S` holds iff the evaluated
matrices `U_g` are unitary, the vectors of tag `1` are unit vectors, `d ≥ 1`, the
lower bounds `‖(S_t(U) - 1) v_t‖² ≥ (1/4)²` hold, and the quadratic forms
`(2^{-n})² ‖u_t‖² - ‖(R_t(U) - 1) u_t‖²` are nonnegative (`qfHolds_encFormula`).
-/

namespace GroupApproximation.Full.NN11b

open GroupApproximation.PresentationCodes Matrix

open scoped Matrix

noncomputable section

/-- The conditions expressed by the matrix of `encFormula P n d S` at `ρ`. -/
def EncCond (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool))) (ρ : ℕ → ℝ) : Prop :=
  ((∀ g : Fin (genCount P), encUmat P ρ d g ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    ∀ t : Fin S.length, ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 1 t d) r) = 1) ∧
  ((1 ≤ d ∧
    ∀ t : Fin S.length, (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
      (((encWordMat P (encUmat P ρ d) (S.getD t []) - 1) *ᵥ encEvalVec ρ d (encVecOf 1 t d)) r)) ∧
    ∀ t : Fin P.2.length,
      0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 2 t d) r)
        - ∑ r : Fin d, Complex.normSq (((encWordMat P (encUmat P ρ d) (P.2.getD t []) - 1) *ᵥ
          encEvalVec ρ d (encVecOf 2 t d)) r))

theorem encUnitEqs_iff (ρ : ℕ → ℝ) (P : PresentationCode) (d : ℕ) :
    (∀ x ∈ encUnitEqs (genCount P) d, mvEval ρ x = 0) ↔
      ∀ g : Fin (genCount P), encUmat P ρ d g ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  constructor
  · intro h g
    refine (Manuscript.MFRecognition.Certificates.mem_unitaryGroup_iff_entry_equations _).2
      fun p q => (cpEval_encUnitEntry P ρ d g p q).1 ((cpEval_eq_zero_iff ρ _).1 ⟨?_, ?_⟩)
    · exact h _ (List.mem_flatMap.2 ⟨(g : ℕ), List.mem_range.2 g.isLt, List.mem_flatMap.2
        ⟨(p : ℕ), List.mem_range.2 p.isLt, List.mem_flatMap.2 ⟨(q : ℕ), List.mem_range.2 q.isLt,
          List.mem_cons_self⟩⟩⟩)
    · exact h _ (List.mem_flatMap.2 ⟨(g : ℕ), List.mem_range.2 g.isLt, List.mem_flatMap.2
        ⟨(p : ℕ), List.mem_range.2 p.isLt, List.mem_flatMap.2 ⟨(q : ℕ), List.mem_range.2 q.isLt,
          List.mem_cons_of_mem _ List.mem_cons_self⟩⟩⟩)
  · intro h x hx
    obtain ⟨g, hg, hx1⟩ := List.mem_flatMap.1 hx
    obtain ⟨p, hp, hx2⟩ := List.mem_flatMap.1 hx1
    obtain ⟨q, hq, hx3⟩ := List.mem_flatMap.1 hx2
    have hz : cpEval ρ (encUnitEntry d g p q) = 0 :=
      (cpEval_encUnitEntry P ρ d ⟨g, List.mem_range.1 hg⟩ ⟨p, List.mem_range.1 hp⟩
        ⟨q, List.mem_range.1 hq⟩).2
        ((Manuscript.MFRecognition.Certificates.mem_unitaryGroup_iff_entry_equations _).1
          (h ⟨g, List.mem_range.1 hg⟩) _ _)
    obtain ⟨hz1, hz2⟩ := (cpEval_eq_zero_iff ρ _).2 hz
    rcases List.mem_cons.1 hx3 with rfl | hx4
    · exact hz1
    · rcases List.mem_cons.1 hx4 with rfl | hx5
      · exact hz2
      · exact absurd hx5 List.not_mem_nil

theorem encUnitNorms_iff (ρ : ℕ → ℝ) (d m : ℕ) :
    (∀ x ∈ (List.range m).map (encUnitNormPoly d), mvEval ρ x = 0) ↔
      ∀ t : Fin m, ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 1 t d) r) = 1 := by
  constructor
  · intro h t
    exact (mvEval_encUnitNormPoly ρ d t).1
      (h _ (List.mem_map.2 ⟨(t : ℕ), List.mem_range.2 t.isLt, rfl⟩))
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact (mvEval_encUnitNormPoly ρ d t).2 (h ⟨t, List.mem_range.1 ht⟩)

theorem encEqs_iff (ρ : ℕ → ℝ) (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool))) :
    (∀ x ∈ encEqs P d S, mvEval ρ x = 0) ↔
      (∀ g : Fin (genCount P), encUmat P ρ d g ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
        ∀ t : Fin S.length, ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 1 t d) r) = 1 := by
  show (∀ x ∈ encUnitEqs (genCount P) d ++ (List.range S.length).map (encUnitNormPoly d),
    mvEval ρ x = 0) ↔ _
  rw [List.forall_mem_append]
  exact and_congr (encUnitEqs_iff ρ P d) (encUnitNorms_iff ρ d S.length)

theorem encLowers_iff (ρ : ℕ → ℝ) (P : PresentationCode) (d : ℕ) (S : List (List (ℕ × Bool))) :
    (∀ x ∈ (List.range S.length).map (fun t => encLowerPoly P d (S.getD t []) t),
      0 ≤ mvEval ρ x) ↔
      ∀ t : Fin S.length, (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
        (((encWordMat P (encUmat P ρ d) (S.getD t []) - 1) *ᵥ encEvalVec ρ d (encVecOf 1 t d)) r) := by
  constructor
  · intro h t
    exact (mvEval_encLowerPoly ρ P d (S.getD t []) t).1
      (h _ (List.mem_map.2 ⟨(t : ℕ), List.mem_range.2 t.isLt, rfl⟩))
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact (mvEval_encLowerPoly ρ P d (S.getD t []) t).2 (h ⟨t, List.mem_range.1 ht⟩)

theorem encUppers_iff (ρ : ℕ → ℝ) (P : PresentationCode) (n d : ℕ) :
    (∀ x ∈ (List.range P.2.length).map (fun t => encUpperPoly P n d (P.2.getD t []) t),
      0 ≤ mvEval ρ x) ↔
      ∀ t : Fin P.2.length,
        0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 2 t d) r)
          - ∑ r : Fin d, Complex.normSq (((encWordMat P (encUmat P ρ d) (P.2.getD t []) - 1) *ᵥ
            encEvalVec ρ d (encVecOf 2 t d)) r) := by
  constructor
  · intro h t
    exact (mvEval_encUpperPoly ρ P n d (P.2.getD t []) t).1
      (h _ (List.mem_map.2 ⟨(t : ℕ), List.mem_range.2 t.isLt, rfl⟩))
  · intro h x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact (mvEval_encUpperPoly ρ P n d (P.2.getD t []) t).2 (h ⟨t, List.mem_range.1 ht⟩)

theorem encNonnegs_iff (ρ : ℕ → ℝ) (P : PresentationCode) (n d : ℕ)
    (S : List (List (ℕ × Bool))) :
    (∀ x ∈ encNonnegs P n d S, 0 ≤ mvEval ρ x) ↔
      (1 ≤ d ∧
        ∀ t : Fin S.length, (1 / 4 : ℝ) ^ 2 ≤ ∑ r : Fin d, Complex.normSq
          (((encWordMat P (encUmat P ρ d) (S.getD t []) - 1) *ᵥ
            encEvalVec ρ d (encVecOf 1 t d)) r)) ∧
      ∀ t : Fin P.2.length,
        0 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 * ∑ r : Fin d, Complex.normSq (encEvalVec ρ d (encVecOf 2 t d) r)
          - ∑ r : Fin d, Complex.normSq (((encWordMat P (encUmat P ρ d) (P.2.getD t []) - 1) *ᵥ
            encEvalVec ρ d (encVecOf 2 t d)) r) := by
  show (∀ x ∈ (mvConst ((d : ℤ) - 1) ::
      (List.range S.length).map fun t => encLowerPoly P d (S.getD t []) t) ++
        (List.range P.2.length).map (fun t => encUpperPoly P n d (P.2.getD t []) t),
    0 ≤ mvEval ρ x) ↔ _
  rw [List.forall_mem_append, List.forall_mem_cons]
  exact and_congr (and_congr (mvEval_encDimPoly ρ d) (encLowers_iff ρ P d S))
    (encUppers_iff ρ P n d)

/-- The matrix of `encFormula P n d S` holds at `ρ` iff `EncCond P n d S ρ`. -/
theorem qfHolds_encFormula (P : PresentationCode) (n d : ℕ) (S : List (List (ℕ × Bool)))
    (ρ : ℕ → ℝ) : qfHolds ρ (encFormula P n d S).2 ↔ EncCond P n d S ρ := by
  show qfHolds ρ (qfAnd [(encEqs P d S).map fun p => (false, p)] (nonnegQF (encNonnegs P n d S)))
    ↔ _
  rw [qfHolds_encSystem]
  exact and_congr (encEqs_iff ρ P d S) (encNonnegs_iff ρ P n d S)

end

end GroupApproximation.Full.NN11b
