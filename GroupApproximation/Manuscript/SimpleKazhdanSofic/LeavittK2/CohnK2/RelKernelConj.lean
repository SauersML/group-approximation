import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelState
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnK2.RelKernelNormal
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Prod
import GroupApproximation.Meta.AxiomGuard

/-!
# One element conjugating every matrix-unit root to a `p`-root (lane `sk-cohn-02`, module 5)

Keep the notation of `RelKernelState.lean`, and let `G L` be the product of the swaps
`relKer_w γ` for `γ ∈ L`.  For duplicate-free `L`, conjugation by `G L` sends
`x_{lo i, lo j}(u(ω s, ω t))` to the state whose flags record whether `(i, s)` and `(j, t)`
lie in `L` (`relKer_G_conj`).  With `L` a list of all of `Fin n × Fin K`, one element `G`
sends every `x_{lo i, lo j}(u(ω s, ω t))` to `x_{hi i s, hi j t}(p)`
(`relKer_G_conj_all`).
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- Membership in `b :: L` for `a ≠ b`. -/
theorem relKer_mem_cons_iff {α : Type*} {a b : α} {L : List α} (h : b ≠ a) :
    a ∈ b :: L ↔ a ∈ L :=
  ⟨fun h' => (List.mem_cons.mp h').resolve_left (fun e => h e.symm),
    fun h' => List.mem_cons_of_mem b h'⟩

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_mem_cons_iff

section Conj

variable {R : Type*} [Ring R] (D : CohnRelativeK1.CohnTwoData R) {n K : ℕ}
  (ω : Fin K → List (Fin 2))

/-- The product of the swaps along a list. -/
def relKer_G (L : List (Fin n × Fin K)) : SteinbergGroup (Fin (n + n * K)) R :=
  (L.map (relKer_w D ω)).prod

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_G

theorem relKer_G_cons (γ : Fin n × Fin K) (L : List (Fin n × Fin K)) :
    relKer_G D ω (γ :: L) = relKer_w D ω γ * relKer_G D ω L := by
  simp only [relKer_G, List.map_cons, List.prod_cons]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_G_cons

/-- **Conjugation along a list.**  The flags of the resulting state record membership of
`(i, s)` and `(j, t)` in `L`. -/
theorem relKer_G_conj (hω : Function.Injective ω) (i j : Fin n) (hij : i ≠ j) (s t : Fin K) :
    ∀ (L : List (Fin n × Fin K)), L.Nodup → ∀ (bi bj : Bool), (bi = true ↔ (i, s) ∈ L) →
      (bj = true ↔ (j, t) ∈ L) →
      relKer_G D ω L * relKer_state D ω i j hij s t false false * (relKer_G D ω L)⁻¹ =
        relKer_state D ω i j hij s t bi bj := by
  intro L
  induction L with
  | nil =>
      intro _ bi bj hbi hbj
      have h0 : relKer_G D ω ([] : List (Fin n × Fin K)) = 1 := by
        simp only [relKer_G, List.map_nil, List.prod_nil]
      rw [h0, one_mul, inv_one, mul_one]
      cases bi
      · cases bj
        · rfl
        · exact absurd (hbj.mp rfl) List.not_mem_nil
      · exact absurd (hbi.mp rfl) List.not_mem_nil
  | cons γ L ih =>
      intro hL bi bj hbi hbj
      obtain ⟨hγL, hL'⟩ := List.nodup_cons.mp hL
      rw [relKer_G_cons, relKer_grp_conj_conj]
      have hIJ : (i, s) ≠ (j, t) := fun h => hij (congrArg Prod.fst h)
      by_cases hγI : γ = (i, s)
      · subst hγI
        have hb : bi = true := hbi.mpr List.mem_cons_self
        rw [ih hL' false bj (iff_of_false (by decide) hγL)
          (hbj.trans (relKer_mem_cons_iff hIJ)), hb]
        exact relKer_stepI D ω i j hij s t bj
      · by_cases hγJ : γ = (j, t)
        · subst hγJ
          have hb : bj = true := hbj.mpr List.mem_cons_self
          rw [ih hL' bi false (hbi.trans (relKer_mem_cons_iff (Ne.symm hIJ)))
            (iff_of_false (by decide) hγL), hb]
          exact relKer_stepJ D ω i j hij s t bi
        · rw [ih hL' bi bj (hbi.trans (relKer_mem_cons_iff hγI))
            (hbj.trans (relKer_mem_cons_iff hγJ))]
          obtain ⟨i', s'⟩ := γ
          exact relKer_stepFix D ω hω i j hij s t i' s' hγI hγJ bi bj

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_G_conj

/-- **One conjugator for all roots.**  With `L` a list of all of `Fin n × Fin K`,
`G L` conjugates `x_{lo i, lo j}(u(ω s, ω t))` to `x_{hi i s, hi j t}(p)`. -/
theorem relKer_G_conj_all (hω : Function.Injective ω) (i j : Fin n) (hij : i ≠ j)
    (s t : Fin K) :
    relKer_G D ω (Finset.univ : Finset (Fin n × Fin K)).toList *
        x (relKer_lo n K i) (relKer_lo n K j) (relKer_lo_ne hij) (D.unit (ω s) (ω t)) *
        (relKer_G D ω (Finset.univ : Finset (Fin n × Fin K)).toList)⁻¹ =
      x (relKer_hi n K i s) (relKer_hi n K j t) (relKer_hi_ne hij s t) D.p :=
  relKer_G_conj D ω hω i j hij s t _ (Finset.nodup_toList _) true true
    (iff_of_true rfl (Finset.mem_toList.mpr (Finset.mem_univ _)))
    (iff_of_true rfl (Finset.mem_toList.mpr (Finset.mem_univ _)))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.relKer_G_conj_all

end Conj

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
