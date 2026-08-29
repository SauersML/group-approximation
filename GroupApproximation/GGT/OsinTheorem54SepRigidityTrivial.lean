import GroupApproximation.GGT.OsinTheorem54SepRigidityReduction

/-!
# The rigidity clause when the second conjugator is known trivial

Split out of `GGT/OsinTheorem54SepRigidityReduction.lean` so that the bounded
lemma there --- `mem_fam_of_conj_of_deep`, which is what a consumer actually
needs --- does not wait on this.

**This does not substitute for the bounded lemma in a consumer's aligned case.**
There, triviality of the connector is a CONCLUSION reached by applying the
rigidity clause twice --- exponent equality, then membership, then the diagonal
clause --- so assuming it here would be circular.  This file is for a consumer
that knows triviality independently.

What it does show is that in that situation the clause is FREE: the two deep
blocks are adjacent in the quadrilateral, which is the corner
`exists_connector_fourGon_run` handles, so the connector is the run itself and
no `IsolatedComponentBound`, no deepness hypothesis and no constant enter.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u

variable {G : Type u} [Group G]

/-- **A letter of the quadrilateral in the reversed block is a letter of
`revWord s`.**  The fourth-block companion of `getElem_mem_fourGon_p` and
`_r`. -/
theorem getElem_mem_fourGon_s (p q r s : List (RelLetter G Bool)) {n : ℕ}
    (h1 : p.length + q.length + r.length ≤ n)
    (hn : n < (p ++ q ++ r ++ revWord s).length) :
    (p ++ q ++ r ++ revWord s)[n]'hn ∈ revWord s := by
  have h2 : (p ++ q ++ r).length ≤ n := by
    rw [List.length_append, List.length_append]
    omega
  rw [List.getElem_append_right h2]
  exact List.getElem_mem _

/-- **When the second conjugator is trivial the clause is free.**

The two deep blocks are then ADJACENT in the quadrilateral, which is the corner
`exists_connector_fourGon_run` handles: they form one run, so the connector is
the run itself and is produced directly --- with no `IsolatedComponentBound`,
no deepness hypothesis, and no constant.

**This does not substitute for the bounded lemma in a consumer's aligned case.**
There, triviality of the connector is a CONCLUSION reached by applying the
rigidity clause twice --- exponent equality, then membership, then the diagonal
clause --- so assuming it here would be circular.  This lemma is for a consumer
that knows triviality independently; `mem_fam_of_conj_of_deep` is the
deliverable. -/
theorem mem_fam_of_conj_trivial (D : RelGenSet G Bool) {a : Bool → G}
    (s : Bool) {i j : ℕ} (px : List (RelLetter G Bool))
    (hlet : ∀ c ∈ (px ++ [RelLetter.comp s (a s ^ i)] ++ [] ++
      revWord [RelLetter.comp s (a s ^ j)]), D.IsLetter c)
    (heq : RelLetter.listVal px * a s ^ i = a s ^ j) :
    RelLetter.listVal px ∈ D.fam s := by
  have hvq : RelLetter.listVal [RelLetter.comp s (a s ^ i)] = a s ^ i := by
    simp [listVal_singleton, RelLetter.val]
  have hvs : RelLetter.listVal [RelLetter.comp s (a s ^ j)] = a s ^ j := by
    simp [listVal_singleton, RelLetter.val]
  have hclose : RelLetter.listVal [RelLetter.comp s (a s ^ j)]
      = RelLetter.listVal px * RelLetter.listVal [RelLetter.comp s (a s ^ i)]
        * RelLetter.listVal ([] : List (RelLetter G Bool)) := by
    rw [hvq, hvs, RelLetter.listVal_nil, mul_one]
    exact heq.symm
  have hlenW : (px ++ [RelLetter.comp s (a s ^ i)] ++ [] ++
      revWord [RelLetter.comp s (a s ^ j)]).length = px.length + 1 + 0 + 1 := by
    rw [length_fourGon]
    simp
  have hn : px.length + 1
      < (px ++ [RelLetter.comp s (a s ^ i)] ++ [] ++
          revWord [RelLetter.comp s (a s ^ j)]).length := by
    rw [hlenW]
    omega
  have hc : ((px ++ [RelLetter.comp s (a s ^ i)] ++ [] ++
      revWord [RelLetter.comp s (a s ^ j)])[px.length + 1]'hn).IsCompOf s := by
    have hmemr := getElem_mem_fourGon_s px [RelLetter.comp s (a s ^ i)] []
      [RelLetter.comp s (a s ^ j)] (by simp) hn
    have hmem1 : ((px ++ [RelLetter.comp s (a s ^ i)] ++ [] ++
        revWord [RelLetter.comp s (a s ^ j)])[px.length + 1]'hn)
        ∈ [RelLetter.comp s ((a s ^ j)⁻¹)] := hmemr
    rw [List.mem_singleton.mp hmem1]
    exact rfl
  obtain ⟨h, hh, hconn⟩ := exists_connector_fourGon_run D s px
    [RelLetter.comp s (a s ^ i)] [] [RelLetter.comp s (a s ^ j)] hclose hlet
    (isComp_singleton s (a s ^ i)) rfl rfl hn hc
  rw [vertex_zero, mul_one] at hconn
  simp only [List.length_singleton, Nat.sub_self, vertex_zero] at hconn
  have hpx : RelLetter.listVal px = h⁻¹ := mul_eq_one_iff_eq_inv.mp hconn
  rw [hpx]
  exact inv_mem hh

end OsinComponents
end GGT
end GroupApproximation
