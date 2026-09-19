import GroupApproximation.GGT.OsinTheorem54SeparatingCosets

/-!
# An admissible path can be taken to read no trivial letter

`relBall` asks for an admissible path, not a reduced one, so a witness may read
a letter whose value is `1`.  For most purposes that costs nothing.  It is fatal
for the polygon of Osin's Lemma 5.8: each peripheral letter of the path becomes
a ONE-LETTER SIDE, and a side has to satisfy `j - i ≤ d(vertexᵢ, vertexⱼ)`,
which at a trivial letter reads `1 ≤ 0`.

So the witness has to be taken of minimal length first, and this module does
that.  Deleting a trivial letter changes nothing that matters: the value is
multiplied by `1`, every later vertex is where it was, so admissibility survives
verbatim, and the word is shorter.  Iterating bottoms out because the lengths
are naturals.

The induction is on a LENGTH BOUND rather than on the word, because the deletion
does not shrink the word structurally --- it rebuilds it as
`w.take j ++ w.drop (j+1)` --- and a bound is what such a recursion descends on.

Osin does not remark on any of this: a path of minimal length visibly has no
trivial edges.  In Lean the minimal witness has to be produced, and the clause
it buys is used once, at the polygon.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.WordMetric

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **Trivial letters can be deleted from an admissible path**, keeping the
endpoints, the admissibility and the length bound. -/
theorem exists_nontrivial_of_avoidsFrom (D : RelGenSet G Λ) (lam : Λ) :
    ∀ (N : ℕ) (w : List (RelLetter G Λ)) (v : G), w.length ≤ N →
      (∀ a ∈ w, D.IsLetter a) → AvoidsFrom D.fam lam w v →
      ∃ u : List (RelLetter G Λ), (∀ a ∈ u, D.IsLetter a) ∧
        RelLetter.listVal u = RelLetter.listVal w ∧
        AvoidsFrom D.fam lam u v ∧ u.length ≤ w.length ∧
        ∀ a ∈ u, a.val ≠ 1 := by
  intro N
  induction N with
  | zero =>
      intro w v hlen hlet hav
      cases w with
      | nil =>
          refine ⟨[], hlet, rfl, hav, le_rfl, ?_⟩
          intro a ha
          simp at ha
      | cons a t => exact absurd hlen (by simp)
  | succ N ih =>
      intro w v hlen hlet hav
      by_cases hall : ∀ a ∈ w, a.val ≠ 1
      · exact ⟨w, hlet, rfl, hav, le_rfl, hall⟩
      · push Not at hall
        obtain ⟨a, ha, haval⟩ := hall
        obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp ha
        have hjval : (w[j]'hj).val = 1 := by
          rw [hja]
          exact haval
        have hdrop : w.drop j = (w[j]'hj) :: w.drop (j + 1) :=
          List.drop_eq_getElem_cons hj
        have hlen' : (w.take j ++ w.drop (j + 1)).length ≤ N := by
          rw [List.length_append, List.length_take, List.length_drop]
          omega
        have hlet' : ∀ b ∈ w.take j ++ w.drop (j + 1), D.IsLetter b := by
          intro b hb
          rcases List.mem_append.mp hb with hb' | hb'
          · exact hlet b (List.take_subset j w hb')
          · exact hlet b (List.drop_subset (j + 1) w hb')
        have hval' : RelLetter.listVal (w.take j ++ w.drop (j + 1))
            = RelLetter.listVal w := by
          have e1 : RelLetter.listVal w
              = RelLetter.listVal (w.take j) * RelLetter.listVal (w.drop j) := by
            rw [← listVal_append, List.take_append_drop]
          have e2 : RelLetter.listVal (w.drop j)
              = RelLetter.listVal (w.drop (j + 1)) := by
            rw [hdrop, listVal_cons, hjval, one_mul]
          rw [listVal_append, e1, e2]
        have hav' : AvoidsFrom D.fam lam (w.take j ++ w.drop (j + 1)) v := by
          have hfull : AvoidsFrom D.fam lam (w.take j ++ w.drop j) v := by
            rw [List.take_append_drop]
            exact hav
          have hboth := (avoidsFrom_append D.fam lam (w.take j) (w.drop j) v).mp
            hfull
          rw [avoidsFrom_append]
          refine ⟨hboth.1, ?_⟩
          have h2 := hboth.2
          rw [hdrop] at h2
          have h3 := h2.2
          rwa [hjval, mul_one] at h3
        obtain ⟨u, hulet, huval, huav, hulen, hunt⟩ :=
          ih (w.take j ++ w.drop (j + 1)) v hlen' hlet' hav'
        refine ⟨u, hulet, ?_, huav, ?_, hunt⟩
        · rw [huval, hval']
        · rw [List.length_append, List.length_take, List.length_drop] at hulen
          omega

/-- **A relative ball is witnessed by a path with no trivial letter.** -/
theorem exists_nontrivial_word_of_mem_relBall (D : RelGenSet G Λ) (lam : Λ)
    {h : G} {n : ℕ} (hmem : h ∈ D.relBall lam n) :
    ∃ w : List (RelLetter G Λ), (∀ a ∈ w, D.IsLetter a) ∧
      RelLetter.listVal w = h ∧ AvoidsFrom D.fam lam w 1 ∧ w.length ≤ n ∧
      ∀ a ∈ w, a.val ≠ 1 := by
  obtain ⟨-, w, hlet, hval, hav, hlen⟩ := hmem
  obtain ⟨u, hulet, huval, huav, hulen, hunt⟩ :=
    exists_nontrivial_of_avoidsFrom D lam w.length w 1 le_rfl hlet hav
  refine ⟨u, hulet, ?_, huav, by omega, hunt⟩
  rw [huval, hval]

end OsinComponents
end GGT
end GroupApproximation
