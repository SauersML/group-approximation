import GroupApproximation.GGT.OsinTheorem54SepSegmentComp

/-!
# Boundary-inclusive restriction of maximal components
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

omit [Group G] in
/-- A component of a word remains a component of a segment containing its
whole span.  At an exposed segment endpoint the corresponding maximality
clause is vacuous. -/
theorem isComp_segment_of_isComp (lam : Λ) (word : List (RelLetter G Λ))
    {start len i finish : ℕ}
    (hcomp : IsComp lam word (start + i) (start + finish))
    (hstart : start + len ≤ word.length)
    (hfinish : finish ≤ len) :
    IsComp lam ((word.drop start).take len) i finish := by
  obtain ⟨hif, hflen, hrange, hprev, hnext⟩ := hcomp
  have hseglen : ((word.drop start).take len).length = len := by
    rw [List.length_take, List.length_drop]
    omega
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro q hiq hqf hq
    have hword : start + q < word.length := by omega
    rw [← getElem_segment' word start len q (start + q) hq hword rfl]
    exact hrange (start + q) (by omega) (by omega) hword
  · intro q heq hq hletter
    have hword : start + q < word.length := by omega
    rw [← getElem_segment' word start len q (start + q) hq hword rfl] at hletter
    exact hprev (start + q) (by omega) hword hletter
  · intro hf hletter
    have hword : start + finish < word.length := by omega
    rw [← getElem_segment' word start len finish (start + finish) hf hword rfl]
      at hletter
    exact hnext hword hletter

end OsinComponents
end GGT
end GroupApproximation
