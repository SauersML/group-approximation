import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonRealization
import GroupApproximation.GGT.HullSCLemma44OriginalExpansion
import GroupApproximation.GGT.HullSCLemma51LetterWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Respelling a word that is not quasi-geodesic

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  The contradiction comes from a strictly shorter spelling of a subword, and
`quasiGeodesicRespellInput` proves `QuasiGeodesicRespellInput`.  Let a legal word over the
symmetric label alphabet fail to be `(λ, c + 2)`-quasi-geodesic, with `λ ≤ 1` and `0 ≤ c`.  A
violating subword of length `n` has end vertices at distance `m` with `m + 2 < n`.
* If `m ≠ 0`, a geodesic spelling of length `m` is shorter.
* If `m = 0`, then `n ≥ 3`, and the subword without its last letter is spelled by the inverse of
  that letter.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.WordMetric

/-- The value of a subword is the step between its end vertices. -/
theorem listVal_drop_take_eq_vertex {G : Type u} [Group G] {Lambda : Type w}
    (word : List (RelLetter G Lambda)) (i n : ℕ) :
    RelLetter.listVal ((word.drop i).take n) =
      (OsinComponents.vertex 1 word i)⁻¹ * OsinComponents.vertex 1 word (i + n) := by
  rw [HullSC.vertex_eq_mul_listVal_take, HullSC.vertex_eq_mul_listVal_take, one_mul, one_mul,
    List.take_add, HullSC.RelWord.listVal_append, inv_mul_cancel_left]

/-- **Respelling a word that is not quasi-geodesic.**  "This contradicts our assumption that
`∑ l(t_i)` is minimal."  A violating subword has a strictly shorter nonempty legal spelling. -/
theorem quasiGeodesicRespellInput : QuasiGeodesicRespellInput.{u, w} := by
  intro G _ Lambda D lambda c hlambda hc word hadm hnot
  obtain ⟨i, j, hij, hj, hlt⟩ : ∃ i j : ℕ, i ≤ j ∧ j ≤ word.length ∧
      ((wordDist (symmetricLabelAlphabet D).alphabet.carrier (OsinComponents.vertex 1 word i)
        (OsinComponents.vertex 1 word j) : ℕ) : ℝ) < lambda * ((j - i : ℕ) : ℝ) - (c + 2) := by
    by_contra hcon
    push Not at hcon
    exact hnot ⟨hadm, hcon⟩
  obtain ⟨n, rfl⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
  rw [Nat.add_sub_cancel_left] at hlt
  obtain ⟨v, hvletter, hval, hlen⟩ := HullSC.exists_word_of_relGenSet (symmetricLabelAlphabet D)
    ((OsinComponents.vertex 1 word i)⁻¹ * OsinComponents.vertex 1 word (i + n))
  have hdist : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex 1 word i) (OsinComponents.vertex 1 word (i + n)) = v.length := by
    rw [hlen]
    rfl
  rw [hdist] at hlt
  have hshort : v.length + 2 < n := by
    have hn : lambda * (n : ℝ) ≤ n := mul_le_of_le_one_left (Nat.cast_nonneg n) hlambda
    have hreal : (v.length : ℝ) + 2 < n := by linarith
    exact_mod_cast hreal
  by_cases hne : v = []
  · subst hne
    rw [List.length_nil] at hshort
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k < (word.drop i).length := by
      rw [List.length_drop]
      omega
    have hone : RelLetter.listVal ((word.drop i).take (k + 1)) = 1 := by
      rw [listVal_drop_take_eq_vertex, ← hval, RelLetter.listVal_nil]
    rw [List.take_succ_eq_append_getElem hk, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_singleton] at hone
    refine ⟨i, k, by omega, [HullSC.invLetter (symmetricLabelAlphabet D) (word.drop i)[k]],
      List.cons_ne_nil _ _, ?_, ?_, ?_⟩
    · rw [List.length_singleton]
      omega
    · intro b hb
      rw [List.mem_singleton] at hb
      subst hb
      exact HullSC.isLetter_invLetter _ (hadm _ (List.mem_of_mem_drop (List.getElem_mem hk)))
    · rw [HullSC.RelWord.listVal_singleton, HullSC.val_invLetter]
      exact (eq_inv_of_mul_eq_one_left hone).symm
  · refine ⟨i, n, hj, v, hne, by omega, hvletter, ?_⟩
    rw [hval, listVal_drop_take_eq_vertex]

#audit_axioms GroupApproximation.GGT.VanKampen.listVal_drop_take_eq_vertex
#audit_axioms GroupApproximation.GGT.VanKampen.quasiGeodesicRespellInput

end GroupApproximation.GGT.VanKampen
