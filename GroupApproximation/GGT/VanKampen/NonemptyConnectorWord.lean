import GroupApproximation.GGT.HullSCRelatorAdmissible
import GroupApproximation.Meta.AxiomGuard

/-!
# Nonempty spellings of short connector words

Only an empty word is replaced, by a legal letter followed by its formal
inverse. The value is unchanged. When epsilon exceeds two, the same strict
connector bound is preserved; no positive-length assumption is imposed on
the original geodesic connector.
-/

namespace GroupApproximation.GGT.VanKampen.NonemptyConnectorWord

open GroupApproximation.HullSC
universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

def word (letter : RelLetter G Lambda) (s : List (RelLetter G Lambda)) :
    List (RelLetter G Lambda) := if s = [] then [letter, RelWord.inv letter] else s

theorem nonempty (letter : RelLetter G Lambda) (s : List (RelLetter G Lambda)) :
    word letter s ≠ [] := by
  unfold word
  split_ifs with h
  · simp
  · exact h

theorem value (letter : RelLetter G Lambda) (s : List (RelLetter G Lambda)) :
    RelLetter.listVal (word letter s) = RelLetter.listVal s := by
  unfold word
  split_ifs with h
  · subst s
    simp [RelLetter.listVal, RelWord.val_inv]
  · rfl

theorem admissible (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (letter : RelLetter G Lambda) (hletter : D.IsLetter letter)
    (s : List (RelLetter G Lambda)) (hs : RelWord.IsAdmissible D s) :
    RelWord.IsAdmissible D (word letter s) := by
  unfold word
  split_ifs
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hletter
    · exact isLetter_relWordInv D hsymm hletter
  · exact hs

theorem length_lt (letter : RelLetter G Lambda) (s : List (RelLetter G Lambda))
    {eps : ℕ} (heps : 2 < eps) (hs : s.length < eps) :
    (word letter s).length < eps := by
  unfold word
  split_ifs
  · exact heps
  · exact hs

end GroupApproximation.GGT.VanKampen.NonemptyConnectorWord

#audit_axioms GroupApproximation.GGT.VanKampen.NonemptyConnectorWord.value
#audit_axioms GroupApproximation.GGT.VanKampen.NonemptyConnectorWord.admissible
#audit_axioms GroupApproximation.GGT.VanKampen.NonemptyConnectorWord.length_lt
