import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVCOrbitAllAtom
import GroupApproximation.Meta.AxiomGuard

/-!
# The path antichain (lane bh-met-91x)

For a word `p`, `higmanVCOrbitAll_pathSet p` holds the siblings along `p`, meaning the words
`q j` with `q y` a prefix of `p` and `j ≠ y`, together with the children `p i` of `p`.  It is
an antichain (`higmanVCOrbitAll_pathSet_isAC`).  For the pivot `t = m(a, b)` and a letter `y`,
the antichain `higmanVCOrbitAll_CP a b p y` is `a · pathSet p ∪ b · pathSet (p y)`.  It is the
antichain of the path atom `m(a p, b p y y)` in `EnvelopeHigmanVCOrbitAllFam`.  For `p = [x]`
and `y = x` it contains the atom antichain `higmanVCOrbitGen_C a b x`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- Siblings along `p`, together with the children of `p`. -/
def higmanVCOrbitAll_pathSet {d : ℕ} : List (Fin d) → Finset (List (Fin d))
  | [] => Finset.univ.image fun i : Fin d => [i]
  | y :: p => (Finset.univ.filter fun j : Fin d => j ≠ y).image (fun j => [j]) ∪
      (higmanVCOrbitAll_pathSet p).image (y :: ·)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_pathSet

/-- The path set is an antichain. -/
theorem higmanVCOrbitAll_pathSet_isAC {d : ℕ} :
    ∀ p : List (Fin d), higmanVCTreeNFWitPivot_IsAC (higmanVCOrbitAll_pathSet p)
  | [] => by
    intro u hu v hv huv h
    simp only [higmanVCOrbitAll_pathSet, Finset.mem_image, Finset.mem_univ, true_and] at hu hv
    obtain ⟨i, rfl⟩ := hu
    obtain ⟨j, rfl⟩ := hv
    exact huv (by rw [(List.cons_prefix_cons.mp h).1])
  | z :: p => by
    intro u hu v hv huv h
    simp only [higmanVCOrbitAll_pathSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and] at hu hv
    rcases hu with ⟨i, hi, rfl⟩ | ⟨e, he, rfl⟩ <;> rcases hv with ⟨j, hj, rfl⟩ | ⟨e', he', rfl⟩
    · exact huv (by rw [(List.cons_prefix_cons.mp h).1])
    · exact hi (List.cons_prefix_cons.mp h).1
    · exact hj (List.cons_prefix_cons.mp h).1.symm
    · exact higmanVCOrbitAll_pathSet_isAC p e he e' he' (fun hee => huv (by rw [hee]))
        (List.cons_prefix_cons.mp h).2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_pathSet_isAC

/-- The children `p i` lie in the path set of `p`. -/
theorem higmanVCOrbitAll_mem_child {d : ℕ} :
    ∀ (p : List (Fin d)) (i : Fin d), p ++ [i] ∈ higmanVCOrbitAll_pathSet p
  | [], i => by
    simp only [List.nil_append, higmanVCOrbitAll_pathSet, Finset.mem_image, Finset.mem_univ,
      true_and]
    exact ⟨i, rfl⟩
  | z :: p, i => by
    rw [List.cons_append, higmanVCOrbitAll_pathSet]
    exact Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨p ++ [i], higmanVCOrbitAll_mem_child p i, rfl⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_mem_child

/-- The siblings `q j` (with `q y` a prefix of `p`, `j ≠ y`) lie in the path set of `p`. -/
theorem higmanVCOrbitAll_mem_sib {d : ℕ} :
    ∀ (p q : List (Fin d)) (y j : Fin d), q ++ [y] <+: p → j ≠ y →
      q ++ [j] ∈ higmanVCOrbitAll_pathSet p
  | [], q, y, _j, hq, _ => by
    have hl : (q ++ [y]).length ≤ ([] : List (Fin d)).length := hq.length_le
    rw [List.length_append, List.length_singleton, List.length_nil] at hl
    omega
  | z :: p, [], y, j, hq, hj => by
    rw [List.nil_append] at hq
    have hyz : y = z := (List.cons_prefix_cons.mp hq).1
    rw [List.nil_append, higmanVCOrbitAll_pathSet]
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, ?_, rfl⟩)
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun h => hj (h.trans hyz.symm)⟩
  | z :: p, r :: q, y, j, hq, hj => by
    rw [List.cons_append] at hq
    have hrz : r = z := (List.cons_prefix_cons.mp hq).1
    rw [List.cons_append, higmanVCOrbitAll_pathSet]
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨q ++ [j], higmanVCOrbitAll_mem_sib p q y j (List.cons_prefix_cons.mp hq).2 hj, by rw [hrz]⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_mem_sib

/-- The path-atom antichain `a · pathSet p ∪ b · pathSet (p y)`. -/
def higmanVCOrbitAll_CP {d : ℕ} (a b p : List (Fin d)) (y : Fin d) :
    Finset (List (Fin d)) :=
  (higmanVCOrbitAll_pathSet p).image (a ++ ·) ∪
    (higmanVCOrbitAll_pathSet (p ++ [y])).image (b ++ ·)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_CP

/-- The path-atom antichain is an antichain. -/
theorem higmanVCOrbitAll_CP_isAC {d : ℕ} {a b : List (Fin d)} (hab : ¬ a <+: b)
    (hba : ¬ b <+: a) (p : List (Fin d)) (y : Fin d) :
    higmanVCTreeNFWitPivot_IsAC (higmanVCOrbitAll_CP a b p y) := by
  have hA := higmanVCOrbitAll_pathSet_isAC p
  have hB := higmanVCOrbitAll_pathSet_isAC (p ++ [y])
  intro u hu v hv huv hpre
  simp only [higmanVCOrbitAll_CP, Finset.mem_union, Finset.mem_image] at hu hv
  rcases hu with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hv with ⟨e', he', rfl⟩ | ⟨e', -, rfl⟩
    · exact hA e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj a).mp hpre)
    · exact higmanVCOrbitGap_incomp_append hab hba e e' hpre
  · rcases hv with ⟨e', -, rfl⟩ | ⟨e', he', rfl⟩
    · exact higmanVCOrbitGap_incomp_append hba hab e e' hpre
    · exact hB e he e' he' (fun h => huv (by rw [h])) ((List.prefix_append_right_inj b).mp hpre)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVCOrbitAll_CP_isAC

end GroupApproximation.BooneHigman.Metabelian.Envelope
