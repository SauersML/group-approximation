import GroupApproximation.BooneHigman.Metabelian.EnvelopeSimpleFragPieces
import GroupApproximation.Meta.AxiomGuard

/-!
# Families of cone swaps made of fragments

For a word `u` with `4 ≤ |u|` and a finite set `T` of words of length `|u|` different from `u`,
`frag_swap_family` builds a product `k` of cone swaps `w ↔ u ++ w` (`w ∈ T`) in the closure of
`fragPieces H`: `k` exchanges `cone w` and `cone (u ++ w)` by prefix substitution and fixes every
stream outside these cones.  Route: `Finset.induction_on`, multiplying by one cone swap (a piece
by `fragPieces_of_long`); the cones involved are pairwise disjoint (`frag_cone_sep`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

open Trees
open HydeLodha

noncomputable section

variable {X : Type*}

/-- Cones of `w`, `u ++ w` avoid the cones of `v`, `u ++ v` for distinct words of length `|u|`
different from `u`. -/
theorem frag_cone_sep {u w v : List X} (hw : w.length = u.length) (hv : v.length = u.length)
    (hwu : w ≠ u) (hvu : v ≠ u) (hwv : w ≠ v) {z : Cantor X}
    (hz : z ∈ cone w ∨ z ∈ cone (u ++ w)) : z ∉ cone v ∧ z ∉ cone (u ++ v) := by
  have dwv : Disjoint (cone w) (cone v) := disjoint_cone_of_length_eq (hw.trans hv.symm) hwv
  have dwu : ∀ a : List X, a.length = u.length → a ≠ u → Disjoint (cone a) (cone u) :=
    fun a ha hau => disjoint_cone_of_length_eq ha hau
  have duvw : Disjoint (cone (u ++ w)) (cone (u ++ v)) :=
    disjoint_cone_of_length_eq (by simp only [List.length_append, hw, hv])
      (fun h => hwv (List.append_cancel_left h))
  rcases hz with hz | hz
  · exact ⟨Set.disjoint_left.mp dwv hz,
      fun h => Set.disjoint_left.mp (dwu w hw hwu) hz (cone_append_subset u v h)⟩
  · have hzu : z ∈ cone u := cone_append_subset u w hz
    exact ⟨fun h => Set.disjoint_left.mp (dwu v hv hvu) h hzu, Set.disjoint_left.mp duvw hz⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_cone_sep

variable [Finite X]

/-- **Swap families.** -/
theorem frag_swap_family (H : Subgroup (TreeAut X)) {u : List X} (hu : 4 ≤ u.length)
    (T : Finset (List X)) (hT : ∀ w ∈ T, w.length = u.length ∧ w ≠ u) :
    ∃ k ∈ Subgroup.closure (fragPieces H),
      (∀ w ∈ T, ∀ y, k (prepend w y) = prepend (u ++ w) y) ∧
      (∀ w ∈ T, ∀ y, k (prepend (u ++ w) y) = prepend w y) ∧
      (∀ x, (∀ w ∈ T, x ∉ cone w ∧ x ∉ cone (u ++ w)) → k x = x) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨1, (Subgroup.closure (fragPieces H)).one_mem,
      fun w hw => absurd hw (Finset.notMem_empty w), fun w hw => absurd hw (Finset.notMem_empty w),
      fun _ _ => rfl⟩
  | insert w₀ T hw₀ ih =>
    have hTp : ∀ w ∈ T, w.length = u.length ∧ w ≠ u :=
      fun w hw => hT w (Finset.mem_insert_of_mem hw)
    obtain ⟨k, hk, h1, h2, h3⟩ := ih hTp
    obtain ⟨hw₀l, hw₀u⟩ := hT w₀ (Finset.mem_insert_self w₀ T)
    have hi1 : ¬ w₀ <+: u ++ w₀ := fun h => hw₀u
      ((List.prefix_of_prefix_length_le h (List.prefix_append u w₀) (le_of_eq hw₀l)).eq_of_length
        hw₀l)
    have hi2 : ¬ u ++ w₀ <+: w₀ := fun h => by
      have hl := h.length_le
      simp only [List.length_append] at hl
      omega
    have hσ : coneSwap w₀ (u ++ w₀) hi1 hi2 ∈ fragPieces H :=
      fragPieces_of_long (higmanThompsonV_le_rn H (coneSwap_mem_higmanThompsonV hi1 hi2))
        (by omega) (by simp only [List.length_append]; omega) (coneSwap_supportedIn hi1 hi2)
    have hfixσ : ∀ z, z ∉ cone w₀ → z ∉ cone (u ++ w₀) →
        coneSwap w₀ (u ++ w₀) hi1 hi2 z = z := by
      intro z hz1 hz2
      refine coneSwap_supportedIn hi1 hi2 z ?_
      rintro (h | h)
      · exact hz1 h
      · exact hz2 h
    have hsep : ∀ w ∈ T, ∀ z, (z ∈ cone w ∨ z ∈ cone (u ++ w)) →
        z ∉ cone w₀ ∧ z ∉ cone (u ++ w₀) := fun w hw z hz =>
      frag_cone_sep (hTp w hw).1 hw₀l (hTp w hw).2 hw₀u (fun h => hw₀ (by rw [← h]; exact hw)) hz
    have hk0 : ∀ w ∈ T, ∀ z, (z ∈ cone w₀ ∨ z ∈ cone (u ++ w₀)) →
        z ∉ cone w ∧ z ∉ cone (u ++ w) := fun w hw z hz =>
      frag_cone_sep hw₀l (hTp w hw).1 hw₀u (hTp w hw).2 (fun h => hw₀ (by rw [h]; exact hw)) hz
    refine ⟨coneSwap w₀ (u ++ w₀) hi1 hi2 * k,
      (Subgroup.closure (fragPieces H)).mul_mem (Subgroup.subset_closure hσ) hk, ?_, ?_, ?_⟩
    · intro w hw y
      rw [Equiv.Perm.mul_apply]
      rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw, h3 (prepend w₀ y) fun w' hw' =>
          hk0 w' hw' (prepend w₀ y) (Or.inl (prepend_mem_cone w₀ y))]
        exact mapsCone_coneSwap_left hi1 hi2 y
      · rw [h1 w hw y]
        have hz := hsep w hw (prepend (u ++ w) y) (Or.inr (prepend_mem_cone (u ++ w) y))
        exact hfixσ _ hz.1 hz.2
    · intro w hw y
      rw [Equiv.Perm.mul_apply]
      rcases Finset.mem_insert.mp hw with hw | hw
      · rw [hw, h3 (prepend (u ++ w₀) y) fun w' hw' =>
          hk0 w' hw' (prepend (u ++ w₀) y) (Or.inr (prepend_mem_cone (u ++ w₀) y))]
        exact mapsCone_coneSwap_right hi1 hi2 y
      · rw [h2 w hw y]
        have hz := hsep w hw (prepend w y) (Or.inl (prepend_mem_cone w y))
        exact hfixσ _ hz.1 hz.2
    · intro x hx
      rw [Equiv.Perm.mul_apply, h3 x fun w hw => hx w (Finset.mem_insert_of_mem hw)]
      have hx0 := hx w₀ (Finset.mem_insert_self w₀ T)
      exact hfixσ x hx0.1 hx0.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.frag_swap_family

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
