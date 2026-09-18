import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSwapRel
import GroupApproximation.Meta.AxiomGuard

/-!
# The split relation for cone swaps (lane bh-met-77)

For incomparable words `v`, `w` and a duplicate-free list `l` of letters containing every letter,
`higmanVFP_splitProd_eq`: `∏_{a ∈ l} (va wa) = (v w)`.

Route, pointwise on the boundary.
* Off `cone v ∪ cone w` every factor is the identity (`higmanVFP_splitProd_fix`).
* A point of `cone v` is `v b z` with `b` its next letter (`higmanVFP_prepend_head`).  The
  factors with `a ≠ b` fix the cones `v b` and `w b` (`higmanVFPSplitSwap_fixLeft/Right`), and
  the unique factor with `a = b` carries `v b z` to `w b z` (`higmanVFP_splitProd_left`).
* Points of `cone w` follow by the symmetry `(va wa) = (wa va)` (`higmanVFP_splitProd_right`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

variable {X : Type*}

/-- Off `cone v ∪ cone w` the split product is the identity. -/
theorem higmanVFP_splitProd_fix {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (l : List X)
    {x : Cantor X} (hv : ¬ IsStreamPrefix v x) (hw : ¬ IsStreamPrefix w x) :
    (l.map (higmanVFPSplitSwap h1 h2)).prod x = x := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, Equiv.Perm.one_apply]
  | cons a l ih =>
    have hva : ¬ IsStreamPrefix (v ++ [a]) x := fun h =>
      hv (IsStreamPrefix.of_prefix (List.prefix_append v [a]) h)
    have hwa : ¬ IsStreamPrefix (w ++ [a]) x := fun h =>
      hw (IsStreamPrefix.of_prefix (List.prefix_append w [a]) h)
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply, ih]
    exact coneSwapFun_of_not hva hwa

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_splitProd_fix

/-- If `b ∉ l`, the split product over `l` fixes the cone `v b` pointwise. -/
theorem higmanVFP_splitProd_fixLeft {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) {b : X}
    (l : List X) (hb : b ∉ l) :
    MapsCone (l.map (higmanVFPSplitSwap h1 h2)).prod (v ++ [b]) (v ++ [b]) := by
  induction l with
  | nil =>
    intro z
    rw [List.map_nil, List.prod_nil, Equiv.Perm.one_apply]
  | cons a l ih =>
    intro z
    have hba : a ≠ b := fun h => hb (List.mem_cons.mpr (Or.inl h.symm))
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply,
      ih (fun h => hb (List.mem_cons_of_mem a h)) z]
    exact higmanVFPSplitSwap_fixLeft h1 h2 hba z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_splitProd_fixLeft

/-- If `l` is duplicate-free and `b ∈ l`, the split product over `l` carries `v b z` to
`w b z`. -/
theorem higmanVFP_splitProd_left {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) {b : X}
    (l : List X) (hl : l.Nodup) (hb : b ∈ l) :
    MapsCone (l.map (higmanVFPSplitSwap h1 h2)).prod (v ++ [b]) (w ++ [b]) := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    intro z
    obtain ⟨hal, hl'⟩ := List.nodup_cons.mp hl
    rw [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    by_cases hab : a = b
    · rw [← hab, higmanVFP_splitProd_fixLeft h1 h2 l hal z]
      exact mapsCone_coneSwap_left (higmanVFP_ext_incomp h1 h2 a a)
        (higmanVFP_ext_incomp h2 h1 a a) z
    · have hbl : b ∈ l := (List.mem_cons.mp hb).resolve_left fun h => hab h.symm
      rw [ih hl' hbl z]
      exact higmanVFPSplitSwap_fixRight h1 h2 hab z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_splitProd_left

/-- If `l` is duplicate-free and `b ∈ l`, the split product over `l` carries `w b z` to
`v b z`. -/
theorem higmanVFP_splitProd_right {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) {b : X}
    (l : List X) (hl : l.Nodup) (hb : b ∈ l) :
    MapsCone (l.map (higmanVFPSplitSwap h1 h2)).prod (w ++ [b]) (v ++ [b]) := by
  have hmap : l.map (higmanVFPSplitSwap h1 h2) = l.map (higmanVFPSplitSwap h2 h1) :=
    List.map_congr_left fun a _ => higmanVFPSplitSwap_comm h1 h2 a
  rw [hmap]
  exact higmanVFP_splitProd_left h2 h1 l hl hb

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_splitProd_right

/-- **The split relation.**  For a duplicate-free list `l` of all letters,
`∏_{a ∈ l} (va wa) = (v w)`. -/
theorem higmanVFP_splitProd_eq {v w : List X} (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (l : List X)
    (hl : l.Nodup) (hall : ∀ a, a ∈ l) :
    (l.map (higmanVFPSplitSwap h1 h2)).prod = coneSwap v w h1 h2 := by
  refine Equiv.ext fun x => ?_
  show _ = coneSwapFun v w x
  by_cases hv : IsStreamPrefix v x
  · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hv
    rw [coneSwapFun_prepend_left, ← higmanVFP_prepend_head y, ← prepend_append,
      ← prepend_append, higmanVFP_splitProd_left h1 h2 l hl (hall (y 0)) (dropN 1 y)]
  · by_cases hw : IsStreamPrefix w x
    · obtain ⟨y, rfl⟩ := mem_cone_iff.mp hw
      rw [coneSwapFun_prepend_right h1 h2, ← higmanVFP_prepend_head y, ← prepend_append,
        ← prepend_append, higmanVFP_splitProd_right h1 h2 l hl (hall (y 0)) (dropN 1 y)]
    · rw [coneSwapFun_of_not hv hw]
      exact higmanVFP_splitProd_fix h1 h2 l hv hw

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_splitProd_eq

end GroupApproximation.BooneHigman.Metabelian.Envelope
