import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPLetters
import GroupApproximation.BooneHigman.Metabelian.EnvelopeHigmanVFPSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# The split relators lie in `higmanVFPRelators d` (lane bh-met-77)

For incomparable words `v`, `w` of length `≤ 2` over `Fin d`, the word
`higmanVFPSplitWord hv hw = ∏_{a ∈ finRange d} ℓ(va, wa)` evaluates to `(v w)`
(`higmanVFP_lift_splitWord`, from the permutation identity `higmanVFP_splitProd_eq`) and has
reduced length `≤ d` (`higmanVFP_norm_splitWord`).  Hence the split relator
`ℓ(v, w) · (∏ₐ ℓ(va, wa))⁻¹`, of reduced length `≤ d + 1 ≤ 8d + 64`, lies in the relator set
(`higmanVFP_letter_split_mem`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- A word of length `≤ 2` has length `≤ 3`. -/
theorem higmanVFP_len_le3 {X : Type*} {v : List X} (h : v.length ≤ 2) : v.length ≤ 3 := by
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_len_le3

/-- A one-letter extension of a word of length `≤ 2` has length `≤ 3`. -/
theorem higmanVFP_len_succ {X : Type*} {v : List X} (h : v.length ≤ 2) (a : X) :
    (v ++ [a]).length ≤ 3 := by
  rw [List.length_append, List.length_singleton]
  omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_len_succ

/-- A product of elements of reduced length `≤ 1` has reduced length at most its length. -/
theorem higmanVFP_norm_prod_le {α : Type*} [DecidableEq α] (l : List (FreeGroup α))
    (h : ∀ x ∈ l, FreeGroup.norm x ≤ 1) : FreeGroup.norm l.prod ≤ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 : FreeGroup.norm a ≤ 1 := h a (List.mem_cons.mpr (Or.inl rfl))
    have h2 : FreeGroup.norm l.prod ≤ l.length :=
      ih fun x hx => h x (List.mem_cons_of_mem a hx)
    have h3 := FreeGroup.norm_mul_le a l.prod
    rw [List.prod_cons, List.length_cons]
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_norm_prod_le

/-- Coercing an evaluated list product into the ambient group. -/
theorem higmanVFP_coe_map_list_prod {F G : Type*} [Group F] [Group G] {H : Subgroup G}
    (φ : F →* ↥H) {ι : Type*} (L : ι → F) (s : ι → G) (h : ∀ a, ((φ (L a) : ↥H) : G) = s a)
    (l : List ι) : ((φ (l.map L).prod : ↥H) : G) = (l.map s).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, Subgroup.coe_one]
  | cons a l ih => simp only [List.map_cons, List.prod_cons, map_mul, Subgroup.coe_mul, h a, ih]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_coe_map_list_prod

/-- The split word `∏_{a ∈ finRange d} ℓ(va, wa)` of the pair `(v, w)`. -/
noncomputable def higmanVFPSplitWord {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 2)
    (hw : w.length ≤ 2) : FreeGroup (Fin (Nat.card ↥(vgenShortPairs (Fin d)))) :=
  ((List.finRange d).map fun a =>
    higmanVFPLetter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)).prod

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFPSplitWord

/-- The letter `ℓ(va, wa)` evaluates to the split factor `(va wa)`. -/
theorem higmanVFP_lift_splitLetter {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 2)
    (hw : w.length ≤ 2) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) (a : Fin d) :
    ((FreeGroup.lift (vgenShortSwaps (Fin d))
        (higmanVFPLetter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)) :
        ↥(higmanThompsonV (Fin d))) : Equiv.Perm (Cantor (Fin d))) =
      higmanVFPSplitSwap h1 h2 a := by
  have h := congrArg Subtype.val
    ((higmanVFP_lift_letter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)).trans
      (vgenSwapOrOne_eq (higmanVFP_ext_incomp h1 h2 a a) (higmanVFP_ext_incomp h2 h1 a a)))
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_lift_splitLetter

/-- The split word evaluates to `(v w)`. -/
theorem higmanVFP_lift_splitWord {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 2)
    (hw : w.length ≤ 2) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) :
    ((FreeGroup.lift (vgenShortSwaps (Fin d)) (higmanVFPSplitWord hv hw) :
        ↥(higmanThompsonV (Fin d))) : Equiv.Perm (Cantor (Fin d))) = coneSwap v w h1 h2 :=
  (higmanVFP_coe_map_list_prod (FreeGroup.lift (vgenShortSwaps (Fin d)))
      (fun a => higmanVFPLetter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a))
      (higmanVFPSplitSwap h1 h2) (higmanVFP_lift_splitLetter hv hw h1 h2)
      (List.finRange d)).trans
    (higmanVFP_splitProd_eq h1 h2 (List.finRange d) (List.nodup_finRange d) List.mem_finRange)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_lift_splitWord

/-- The split word has reduced length `≤ d`. -/
theorem higmanVFP_norm_splitWord {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 2)
    (hw : w.length ≤ 2) : FreeGroup.norm (higmanVFPSplitWord hv hw) ≤ d := by
  have h := higmanVFP_norm_prod_le ((List.finRange d).map fun a =>
      higmanVFPLetter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)) (by
    intro x hx
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    exact (higmanVFP_norm_letter (higmanVFP_len_succ hv a) (higmanVFP_len_succ hw a)).le)
  rw [List.length_map, List.length_finRange] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_norm_splitWord

/-- **Split relators.**  For incomparable `v`, `w` of length `≤ 2`,
`ℓ(v, w) · (∏ₐ ℓ(va, wa))⁻¹` is a relator. -/
theorem higmanVFP_letter_split_mem {d : ℕ} {v w : List (Fin d)} (hv : v.length ≤ 2)
    (hw : w.length ≤ 2) (h1 : ¬ v <+: w) (h2 : ¬ w <+: v) :
    higmanVFPLetter (higmanVFP_len_le3 hv) (higmanVFP_len_le3 hw) *
      (higmanVFPSplitWord hv hw)⁻¹ ∈ higmanVFPRelators d := by
  refine ⟨MonoidHom.mem_ker.mpr ?_, ?_⟩
  · rw [map_mul, map_inv, mul_inv_eq_one, higmanVFP_lift_letter, vgenSwapOrOne_eq h1 h2]
    exact Subtype.ext (higmanVFP_lift_splitWord hv hw h1 h2).symm
  · have hn := FreeGroup.norm_mul_le (higmanVFPLetter (higmanVFP_len_le3 hv)
      (higmanVFP_len_le3 hw)) (higmanVFPSplitWord hv hw)⁻¹
    rw [FreeGroup.norm_inv_eq, higmanVFP_norm_letter] at hn
    have hs := higmanVFP_norm_splitWord hv hw
    unfold higmanVFPBound
    omega

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.higmanVFP_letter_split_mem

end GroupApproximation.BooneHigman.Metabelian.Envelope
