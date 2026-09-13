import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.VanKampen.SymmetricLabelAlphabet
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.GGT.HullSCRelatorFamily
import GroupApproximation.Meta.AxiomGuard

/-!
# Respelling a word that is not quasi-geodesic

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)`
is minimal."  The cutting paths of a family with the fewest darts are `(λ, c + 2)`-quasi-geodesic:
otherwise a subpath has a strictly shorter nonempty legal spelling, and `ChainRespellInput`
respells it with fewer darts.  This file proves the word-metric half.

`exists_shorter_respelling_of_not_isLambdaCQuasiGeodesicWord`: a legal word over the symmetric
label alphabet that is not `(λ, c + 2)`-quasi-geodesic, with `λ ≤ 1` and `0 ≤ c`, has a subword
`(word.drop i).take n` with a strictly shorter nonempty legal spelling.  Its binders are those of
`QuasiGeodesicRespellInput`.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.WordMetric

/-- **Respelling a word that is not quasi-geodesic.**  Let `word` be legal over the symmetric
label alphabet and not `(λ, c + 2)`-quasi-geodesic, with `λ ≤ 1` and `0 ≤ c`.  Then some subword
`(word.drop i).take n` has a strictly shorter nonempty legal spelling.

A violating subword has `n` letters and a value `g` with `|g| + 2 < n`.  If `g ≠ 1`, a geodesic
spelling of `g` is nonempty and has `|g|` letters.  If `g = 1`, then `n ≥ 3`, and the subword
without its last letter `a` is spelled by the inverse of `a`.  That letter is legal since the base
of the symmetric label alphabet is closed under inverses. -/
theorem exists_shorter_respelling_of_not_isLambdaCQuasiGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda) (lambda c : ℝ)
    (hlambda : lambda ≤ 1) (hc : 0 ≤ c) (word : List (RelLetter G Lambda))
    (hword : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) word)
    (hnot : ¬ IsLambdaCQuasiGeodesicWord (symmetricLabelAlphabet D) lambda (c + 2) word) :
    ∃ i n : ℕ, i + n ≤ word.length ∧ ∃ respelling : List (RelLetter G Lambda),
      respelling ≠ [] ∧ respelling.length < n ∧
        HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) respelling ∧
        RelLetter.listVal respelling = RelLetter.listVal ((word.drop i).take n) := by
  obtain ⟨i, j, hij, hj, hlt⟩ : ∃ i j : ℕ, i ≤ j ∧ j ≤ word.length ∧
      ((wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (GGT.OsinComponents.vertex 1 word i) (GGT.OsinComponents.vertex 1 word j) : ℕ) : ℝ) <
        lambda * ((j - i : ℕ) : ℝ) - (c + 2) := by
    by_contra hall
    exact hnot ⟨hword, fun i j hij hj => not_lt.mp fun hlt => hall ⟨i, j, hij, hj, hlt⟩⟩
  obtain ⟨n, rfl⟩ : ∃ n, j = i + n := ⟨j - i, by omega⟩
  have hdist : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (GGT.OsinComponents.vertex 1 word i) (GGT.OsinComponents.vertex 1 word (i + n)) =
        wordDist (symmetricLabelAlphabet D).alphabet.carrier 1
          (RelLetter.listVal ((word.drop i).take n)) := by
    have h := wordDist_left_invariant (symmetricLabelAlphabet D).alphabet.carrier
      (RelLetter.listVal (word.take i)) 1 (RelLetter.listVal ((word.drop i).take n))
    rw [mul_one] at h
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take,
      GGT.OsinComponents.vertex_eq_mul_listVal_take, List.take_add,
      HullSC.RelWord.listVal_append, one_mul, one_mul, h]
  obtain ⟨g, hg⟩ : ∃ g, RelLetter.listVal ((word.drop i).take n) = g := ⟨_, rfl⟩
  rw [hdist, Nat.add_sub_cancel_left, hg] at hlt
  have hn : wordDist (symmetricLabelAlphabet D).alphabet.carrier 1 g + 2 < n := by
    have h0 : (0 : ℝ) ≤ n := by positivity
    have hscale : lambda * (n : ℝ) ≤ n := by nlinarith
    have hreal :
        ((wordDist (symmetricLabelAlphabet D).alphabet.carrier 1 g : ℕ) : ℝ) + 2 < n := by
      linarith
    exact_mod_cast hreal
  by_cases hg1 : g = 1
  · subst hg1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m < (word.drop i).length := by
      rw [List.length_drop]
      omega
    rw [List.take_succ_eq_append_getElem hm, HullSC.RelWord.listVal_append,
      HullSC.RelWord.listVal_cons, RelLetter.listVal_nil, mul_one] at hg
    refine ⟨i, m, by omega, [HullSC.RelWord.inv ((word.drop i)[m]'hm)], List.cons_ne_nil _ _,
      ?_, ?_, ?_⟩
    · rw [List.length_singleton]
      omega
    · refine fun b hb => ?_
      rw [List.mem_singleton] at hb
      subst hb
      exact HullSC.RelWord.isLetter_inv (symmetricLabelAlphabet.symmetric D)
        (hword _ (List.mem_of_mem_drop (List.getElem_mem hm)))
    · rw [HullSC.RelWord.listVal_cons, RelLetter.listVal_nil, mul_one, HullSC.RelWord.val_inv]
      exact (eq_inv_of_mul_eq_one_left hg).symm
  · obtain ⟨respelling, hletters, hvalue, hlength⟩ :=
      GGT.OsinComponents.existsGeodesicWord (symmetricLabelAlphabet D) 1 g
    rw [one_mul] at hvalue
    refine ⟨i, n, hj, respelling, ?_, by omega, hletters, by rw [hvalue, hg]⟩
    rintro rfl
    rw [RelLetter.listVal_nil] at hvalue
    exact hg1 hvalue.symm

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_shorter_respelling_of_not_isLambdaCQuasiGeodesicWord
