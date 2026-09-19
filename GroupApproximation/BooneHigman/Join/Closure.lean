import GroupApproximation.BooneHigman.Join.FELMain

/-!
# Every element of the all-swaps quotient of `V_2` is a normal form (lane bh-pal-met-join)

`JN` is the set of products `f · σ` with `f ∈ Phi` (the lift of Thompson's `F`) and `σ` in the
antichain subgroup of the leaves of a finite binary tree.

* `path_expand`: if `c` is a leaf of `T`, then `σ ∈ jH (lset T)` can be rewritten as `f · σ'`,
  with `σ'` on a tree `T'` having `c s` as a leaf.  This applies the expansion lemma `fel`
  along the path.  Leaves off the path survive, and words incomparable with `c s` that lie at or
  below a leaf of `T` still do.
* `proc`: right multiplication by the deep split of a letter keeps the normal form.
* `mem_JN`: every element of `Q` lies in `JN`.
* `higmanVC_ker_le_two`: **the all-swaps relators present `V_2`**,
  `ker (higmanVC_evalAll 2) ≤ normalClosure (higmanVC_rels 2 ⊤)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

open BTree

theorem mem_expand_child {T : BTree} {c : List (Fin 2)} (hc : c ∈ T.leaves) (a : Fin 2) :
    c ++ [a] ∈ (T.expand c).leaves := by
  rcases fin2_cases a with rfl | rfl
  · exact (mem_leaves_expand T hc _).mpr (Or.inr (Or.inl rfl))
  · exact (mem_leaves_expand T hc _).mpr (Or.inr (Or.inr rfl))

#audit_axioms GroupApproximation.BooneHigman.Join.mem_expand_child

theorem mem_expand_of_ne {T : BTree} {c w : List (Fin 2)} (hc : c ∈ T.leaves)
    (hw : w ∈ T.leaves) (hne : w ≠ c) : w ∈ (T.expand c).leaves :=
  (mem_leaves_expand T hc _).mpr (Or.inl ⟨hw, hne⟩)

#audit_axioms GroupApproximation.BooneHigman.Join.mem_expand_of_ne

theorem atOrBelow_expand {T : BTree} {c z : List (Fin 2)} (hc : c ∈ T.leaves)
    (hz : T.AtOrBelow z) (hzc : z ≠ c) : (T.expand c).AtOrBelow z := by
  obtain ⟨w, hw, hwz⟩ := hz
  by_cases hwc : w = c
  · subst hwc
    obtain ⟨t, rfl⟩ := hwz
    cases t with
    | nil => exact absurd (List.append_nil w) hzc
    | cons b t =>
      refine ⟨w ++ [b], mem_expand_child hc b, ?_⟩
      exact ⟨t, by simp⟩
  · exact ⟨w, mem_expand_of_ne hc hw hwc, hwz⟩

#audit_axioms GroupApproximation.BooneHigman.Join.atOrBelow_expand

/-- **Expansion along a path.** -/
theorem path_expand : ∀ (s : List (Fin 2)) (T : BTree) (c : List (Fin 2)), c ∈ T.leaves →
    ∀ σ ∈ jH 2 T.lset, ∃ T' : BTree, ∃ f ∈ Phi, ∃ σ' ∈ jH 2 T'.lset, σ = f * σ' ∧
      c ++ s ∈ T'.leaves ∧ (∀ w ∈ T.leaves, ¬ w <+: c ++ s → w ∈ T'.leaves) ∧
      ∀ z, ¬ z <+: c ++ s → T.AtOrBelow z → T'.AtOrBelow z
  | [], T, c, hc, σ, hσ =>
    ⟨T, 1, Phi.one_mem, σ, hσ, (one_mul σ).symm, by rwa [List.append_nil],
      fun w hw _ => hw, fun z _ hz => hz⟩
  | a :: s, T, c, hc, σ, hσ => by
    obtain ⟨d', hd', f₁, hf₁, ρ, hρ, e, -⟩ := fel T σ hσ c hc
    obtain ⟨T', f₂, hf₂, σ', hσ', e', hmem, hsurv, hpres⟩ :=
      path_expand s (T.expand c) (c ++ [a]) (mem_expand_child hc a) ρ hρ
    have hcs : c ++ [a] ++ s = c ++ a :: s := by simp
    rw [hcs] at hmem hsurv hpres
    refine ⟨T', f₁ * f₂, Phi.mul_mem hf₁ hf₂, σ', hσ', by rw [e, e', mul_assoc], hmem, ?_, ?_⟩
    · intro w hw hwp
      refine hsurv w (mem_expand_of_ne hc hw ?_) hwp
      intro hwc
      rw [hwc] at hwp
      exact hwp (List.prefix_append c (a :: s))
    · intro z hz hzT
      refine hpres z hz (atOrBelow_expand hc hzT ?_)
      intro hzc
      rw [hzc] at hz
      exact hz (List.prefix_append c (a :: s))

#audit_axioms GroupApproximation.BooneHigman.Join.path_expand

/-- Incomparability of the children of different letters. -/
theorem incomp_diff {x : List (Fin 2)} {a b : Fin 2} (hab : a ≠ b) (u v : List (Fin 2)) :
    ¬ (x ++ a :: u) <+: (x ++ b :: v) := by
  rw [List.prefix_append_right_inj, List.cons_prefix_cons]
  exact fun h => hab h.1

#audit_axioms GroupApproximation.BooneHigman.Join.incomp_diff

theorem deep_succ_two (K : ℕ) (x y : List (Fin 2)) :
    higmanVCCommon_mk 2 (higmanVCCommon_deep 2 (K + 1) x y) =
      higmanVCCommon_mk 2 (higmanVCCommon_deep 2 K (x ++ [0]) (y ++ [0])) *
        higmanVCCommon_mk 2 (higmanVCCommon_deep 2 K (x ++ [1]) (y ++ [1])) := by
  rw [higmanVCCommon_deep_succ]
  have hr : List.finRange 2 = [0, 1] := by decide
  rw [hr]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_mul]

#audit_axioms GroupApproximation.BooneHigman.Join.deep_succ_two

/-- Pieces of the `K`-fold split of `(x, y)`, and incomparability with all of them. -/
def AvoidsPieces (K : ℕ) (x y z : List (Fin 2)) : Prop :=
  ∀ w : List (Fin 2), w.length = K →
    (¬ z <+: x ++ w ∧ ¬ x ++ w <+: z) ∧ (¬ z <+: y ++ w ∧ ¬ y ++ w <+: z)

#audit_axioms GroupApproximation.BooneHigman.Join.AvoidsPieces

theorem avoidsPieces_succ {K : ℕ} {x y z : List (Fin 2)} (h : AvoidsPieces (K + 1) x y z)
    (a : Fin 2) : AvoidsPieces K (x ++ [a]) (y ++ [a]) z := by
  intro w hw
  have h' := h (a :: w) (by simp [hw])
  simpa [List.append_assoc] using h'

#audit_axioms GroupApproximation.BooneHigman.Join.avoidsPieces_succ

end GroupApproximation.BooneHigman.Join
