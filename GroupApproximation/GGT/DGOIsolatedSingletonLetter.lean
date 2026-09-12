import GroupApproximation.GGT.DGOAssemblyIsolation
import GroupApproximation.Meta.AxiomGuard

/-!
# Letter-level separation from an isolated singleton component

An auxiliary-cycle cut may create a new component start inside a component
of its parent path. The parent's isolation is still usable: a same-label
letter whose initial or terminal vertex lies in the singleton's coset must be
that singleton's own letter. No maximality of the transported opponent is
needed.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A same-label letter with either endpoint in an isolated singleton's coset
is the singleton itself. -/
theorem eq_of_isolated_singleton_of_connected_letter
    (D : RelGenSet G Lambda) {word : List (RelLetter G Lambda)} {v : G}
    {lam : Lambda} {i m z : ℕ}
    (hlet : ∀ letter ∈ word, D.IsLetter letter)
    (hcomp : IsComp lam word i (i + 1)) (hiso : IsIsolated D.fam lam v word i)
    (hm : m < word.length) (hmz : m ≤ z) (hzm : z ≤ m + 1)
    (hletter : (word[m]'hm).IsCompOf lam)
    (hconn : Connected D.fam lam v word i z) : m = i := by
  obtain ⟨a, k, ham, hmk, haComp⟩ := exists_isComp_of_isCompOf lam word m hm hletter
  have hspan : Connected D.fam lam v word a z := by
    exact span_mem_fam D lam v hlet z (by omega) a (by omega)
      (fun q haq hqz hq => haComp.2.2.1 q haq (by omega) hq)
  have hia : Connected D.fam lam v word i a := connected_trans hconn (connected_symm hspan)
  have hai : a = i := by
    by_contra hne
    exact hiso.2 a hne ⟨k, haComp⟩ hia
  subst a
  have hk := isComp_end_unique haComp hcomp
  omega

/-- In particular, no other same-label letter has its initial vertex in the
isolated singleton's coset. -/
theorem not_connected_of_isolated_singleton_of_isCompOf
    (D : RelGenSet G Lambda) {word : List (RelLetter G Lambda)} {v : G}
    {lam : Lambda} {i m : ℕ}
    (hlet : ∀ letter ∈ word, D.IsLetter letter)
    (hcomp : IsComp lam word i (i + 1)) (hiso : IsIsolated D.fam lam v word i)
    (hm : m < word.length) (hne : m ≠ i) (hletter : (word[m]'hm).IsCompOf lam) :
    ¬ Connected D.fam lam v word i m := by
  intro hconn
  exact hne (eq_of_isolated_singleton_of_connected_letter D hlet hcomp hiso hm
    le_rfl (Nat.le_succ _) hletter hconn)

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.eq_of_isolated_singleton_of_connected_letter
#audit_axioms GroupApproximation.GGT.OsinComponents.not_connected_of_isolated_singleton_of_isCompOf
