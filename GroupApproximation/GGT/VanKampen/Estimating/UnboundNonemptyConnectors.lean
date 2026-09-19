import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors
import GroupApproximation.GGT.VanKampen.NonemptyConnectorWord

/-!
# Nonempty connectors at the already chosen Osin scale

An empty geodesic is replaced by a two-letter ambient null word. The actual
epsilon exceeds two, so both strict connector bounds and the target-prefix
shortening remain valid. The original geodesic pair is retained unchanged.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.WordMetric GroupApproximation.HullSC OsinComponents
universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

theorem OsinUnboundScale.cayley_epsilon_gt_two
    {delta lambda c mu kappa : ℝ} {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * ((delta + 6) + 1))
      (100000 * ((delta + 6) + 1)) eps rho)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa) : 2 < eps := by
  have h : (2 : ℝ) < eps := by linarith [scale.epsilon_large]
  exact_mod_cast h

variable {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}

structure NonemptyConnectors (C : WordConnectorPair D v word n A B eps) where
  startWord : List (RelLetter G Lambda)
  endWord : List (RelLetter G Lambda)
  start_nonempty : startWord ≠ []
  end_nonempty : endWord ≠ []
  start_admissible : RelWord.IsAdmissible D startWord
  end_admissible : RelWord.IsAdmissible D endWord
  start_value : RelLetter.listVal startWord = RelLetter.listVal C.startConnector
  end_value : RelLetter.listVal endWord = RelLetter.listVal C.endConnector
  start_short : startWord.length < eps
  end_short : endWord.length < eps

theorem WordConnectorPair.exists_legal_letter (C : WordConnectorPair D v word n A B eps) :
    ∃ letter : RelLetter G Lambda, D.IsLetter letter := by
  have hne : word C.source ≠ [] := by
    intro h
    have hle := C.a'_le
    have hlt := C.source_forward
    rw [h, List.length_nil] at hle
    omega
  exact ⟨(word C.source).head hne, C.source_admissible _ (List.head_mem hne)⟩

theorem WordConnectorPair.exists_nonempty_connectors (C : WordConnectorPair D v word n A B eps)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (heps : 2 < eps) : Nonempty (NonemptyConnectors C) := by
  obtain ⟨letter, hletter⟩ := C.exists_legal_letter
  exact ⟨{
    startWord := NonemptyConnectorWord.word letter C.startConnector
    endWord := NonemptyConnectorWord.word letter C.endConnector
    start_nonempty := NonemptyConnectorWord.nonempty _ _
    end_nonempty := NonemptyConnectorWord.nonempty _ _
    start_admissible := NonemptyConnectorWord.admissible D hsymm letter hletter _ C.start_geodesic.1
    end_admissible := NonemptyConnectorWord.admissible D hsymm letter hletter _ C.end_geodesic.1
    start_value := NonemptyConnectorWord.value _ _
    end_value := NonemptyConnectorWord.value _ _
    start_short := NonemptyConnectorWord.length_lt _ _ heps C.start_short
    end_short := NonemptyConnectorWord.length_lt _ _ heps C.end_short }⟩

/-- The required nonempty words follow at the actual scale, with no new constants. -/
theorem WordConnectorPair.nonempty_connectors_at_scale (C : WordConnectorPair D v word n A B eps)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    {delta lambda c mu kappa : ℝ} {rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * ((delta + 6) + 1))
      (100000 * ((delta + 6) + 1)) eps rho)
    (hdelta : 0 ≤ delta) (hkappa : 0 ≤ kappa) : Nonempty (NonemptyConnectors C) :=
  C.exists_nonempty_connectors hsymm (scale.cayley_epsilon_gt_two hdelta hkappa)

namespace NonemptyConnectors

variable {C : WordConnectorPair D v word n A B eps} (P : NonemptyConnectors C)

theorem start_transport :
    vertex (v C.target) (word C.target) C.b * RelLetter.listVal P.startWord =
      vertex (v C.source) (word C.source) C.a := by
  rw [P.start_value]
  exact C.start_geodesic.2.1

theorem end_transport :
    vertex (v C.source) (word C.source) C.a' * RelLetter.listVal P.endWord =
      vertex (v C.target) (word C.target) C.b' := by
  rw [P.end_value]
  exact C.end_geodesic.2.1

def boundaryWord : List (RelLetter G Lambda) :=
  C.sourceWord ++ P.endWord ++ RelWord.revInv C.targetWord ++ P.startWord

theorem boundaryWord_value : RelLetter.listVal P.boundaryWord = 1 := by
  have h := C.boundaryWord_value
  simpa only [boundaryWord, WordConnectorPair.boundaryWord, RelWord.listVal_append,
    P.start_value, P.end_value] using h

theorem boundaryWord_admissible (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    RelWord.IsAdmissible D P.boundaryWord := by
  have hsource := orientedWordSegment_admissible hsymm C.source_admissible C.a C.a'
  have htarget := isAdmissible_revInv hsymm
    (orientedWordSegment_admissible hsymm C.target_admissible C.b C.b')
  intro x hx
  simp only [boundaryWord, List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact hsource x hx
  · exact P.end_admissible x hx
  · exact htarget x hx
  · exact P.start_admissible x hx

include P in
theorem exists_shorter_target_prefix (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    ∃ k : ℕ, (k = C.a ∨ k = C.a') ∧
      ∃ s : List (RelLetter G Lambda), s ≠ [] ∧ RelWord.IsAdmissible D s ∧ s.length < eps ∧
        vertex (v C.target) (word C.target) (min C.b C.b') * RelLetter.listVal s =
          vertex (v C.source) (word C.source) k ∧
        RelWord.IsAdmissible D ((word C.target).take (min C.b C.b') ++ s) ∧
        v C.target * RelLetter.listVal ((word C.target).take (min C.b C.b') ++ s) =
          vertex (v C.source) (word C.source) k ∧
        ((word C.target).take (min C.b C.b') ++ s).length < (word C.target).length := by
  have hlong := (C.segment_lengths hsymm).2
  rw [WordConnectorPair.targetWord, orientedWordSegment_length _ C.b_le C.b'_le] at hlong
  have build (k : ℕ) (hk : k = C.a ∨ k = C.a') (s : List (RelLetter G Lambda))
      (hne : s ≠ []) (hs : RelWord.IsAdmissible D s) (hlen : s.length < eps)
      (htransport : vertex (v C.target) (word C.target) (min C.b C.b') * RelLetter.listVal s =
        vertex (v C.source) (word C.source) k) :
      ∃ k : ℕ, (k = C.a ∨ k = C.a') ∧
        ∃ s : List (RelLetter G Lambda), s ≠ [] ∧ RelWord.IsAdmissible D s ∧ s.length < eps ∧
          vertex (v C.target) (word C.target) (min C.b C.b') * RelLetter.listVal s =
            vertex (v C.source) (word C.source) k ∧
          RelWord.IsAdmissible D ((word C.target).take (min C.b C.b') ++ s) ∧
          v C.target * RelLetter.listVal ((word C.target).take (min C.b C.b') ++ s) =
            vertex (v C.source) (word C.source) k ∧
          ((word C.target).take (min C.b C.b') ++ s).length < (word C.target).length := by
    refine ⟨k, hk, s, hne, hs, hlen, htransport, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact C.target_admissible x (List.take_subset _ _ hx)
      · exact hs x hx
    · rw [RelWord.listVal_append, ← mul_assoc, ← vertex_eq_mul_listVal_take]
      exact htransport
    · rw [List.length_append, List.length_take]
      have hb := C.b_le
      have hb' := C.b'_le
      omega
  by_cases hbb' : C.b ≤ C.b'
  · apply build C.a (Or.inl rfl) P.startWord P.start_nonempty P.start_admissible P.start_short
    simpa only [min_eq_left hbb'] using P.start_transport
  · have hb'b : C.b' ≤ C.b := by omega
    apply build C.a' (Or.inr rfl) (RelWord.revInv P.endWord)
    · intro h
      have hlen := congrArg List.length h
      rw [RelWord.length_revInv, List.length_nil] at hlen
      exact P.end_nonempty (List.length_eq_zero_iff.mp hlen)
    · exact isAdmissible_revInv hsymm P.end_admissible
    · simpa only [RelWord.length_revInv] using P.end_short
    · rw [min_eq_right hb'b, RelWord.listVal_revInv, ← P.end_transport]
      group

end NonemptyConnectors
end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.nonempty_connectors_at_scale
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.NonemptyConnectors.boundaryWord_value
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.NonemptyConnectors.exists_shorter_target_prefix
