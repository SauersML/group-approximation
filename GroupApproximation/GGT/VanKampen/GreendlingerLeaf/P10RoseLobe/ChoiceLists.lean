import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.RegionColour
import GroupApproximation.Meta.AxiomGuard

/-!
# One removed dart: block and placement

Lane gl-p10-63.  List facts for the singleton cases of `roseLobeChoice_Statement`: a nodup walk
`c = A ++ [d] ++ C`, a predicate `Q` ("kept") false at `d` and true on `A ++ C`, is one block of
`c` (`roseLobeRegion_Block`), and it is placed (`roseLobeRegion_Place`) as soon as `d` is not an
inner dart of `I` and, if `d` is on `T`, the block is at the end of `c`.

* `roseLobeChoice_ne_of_mem`, `roseLobeChoice_mem_AC_of_ne`: the two sides of the split.
* `roseLobeChoice_split_end`: a split at `d`, at the end of `c` if `d` ends `T`.
* `roseLobeChoice_block_single`, `roseLobeChoice_place_single`: the block and placement clauses.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section ChoiceLists

variable {α : Type*}

/-- In a nodup list `A ++ [d] ++ C`, no dart of `A ++ C` is `d`. -/
theorem roseLobeChoice_ne_of_mem {c A C : List α} {d e : α} (hc : c = A ++ [d] ++ C)
    (hnd : c.Nodup) (he : e ∈ A ++ C) : e ≠ d := by
  intro h
  rw [h] at he
  rw [hc, List.append_assoc, List.singleton_append] at hnd
  exact (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1 he

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_ne_of_mem

/-- A dart of `A ++ [d] ++ C` other than `d` lies in `A ++ C`. -/
theorem roseLobeChoice_mem_AC_of_ne {c A C : List α} {d e : α} (hc : c = A ++ [d] ++ C)
    (he : e ∈ c) (hne : e ≠ d) : e ∈ A ++ C := by
  rw [hc] at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left C h
    · exact absurd (List.mem_singleton.mp h) hne
  · exact List.mem_append_right A h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_mem_AC_of_ne

/-- **A split of `c = P ++ T` at `d`**, taken at the very end of `c` when `d` ends `T`. -/
theorem roseLobeChoice_split_end {c P T : List α} {d : α} (hdec : c = P ++ T) (hd : d ∈ c)
    (hT : d ∉ T ∨ [d] <:+ T) : ∃ A C : List α, c = A ++ [d] ++ C ∧ (d ∉ T ∨ C = []) := by
  rcases hT with hT | ⟨t, ht⟩
  · obtain ⟨A, C, h⟩ := List.append_of_mem hd
    refine ⟨A, C, ?_, Or.inl hT⟩
    rw [h]
    simp
  · refine ⟨P ++ t, [], ?_, Or.inr rfl⟩
    rw [hdec, ← ht]
    simp

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_split_end

/-- **A split of `c = P ++ T` at `d`**, with nothing of `T` before `d` when `d` starts `T`. -/
theorem roseLobeChoice_split_start {c P T : List α} {d : α} (hdec : c = P ++ T)
    (hnd : c.Nodup) (hd : d ∈ c) (hT : d ∉ T ∨ [d] <+: T) :
    ∃ A C : List α, c = A ++ [d] ++ C ∧ (d ∉ T ∨ ∀ e ∈ A, e ∉ T) := by
  rcases hT with hT | ⟨t, ht⟩
  · obtain ⟨A, C, h⟩ := List.append_of_mem hd
    refine ⟨A, C, ?_, Or.inl hT⟩
    rw [h]
    simp
  · have hnd' : (P ++ T).Nodup := by
      rw [← hdec]
      exact hnd
    refine ⟨P, t, ?_, Or.inr fun e he heT => (List.nodup_append.mp hnd').2.2 e he e heT rfl⟩
    rw [hdec, ← ht]
    simp

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_split_start

/-- **One removed dart is a block**: `Q` false at `d` and true on the nonempty rest. -/
theorem roseLobeChoice_block_single {c A C : List α} {d : α} {Q : α → Prop}
    (hc : c = A ++ [d] ++ C) (hne : A ++ C ≠ []) (hd : ¬Q d) (hQ : ∀ e ∈ A ++ C, Q e) :
    roseLobeRegion_Block c Q A [d] C := by
  unfold roseLobeRegion_Block
  refine ⟨hc, Or.inl ⟨?_, hQ, hne⟩⟩
  intro e he
  rw [List.mem_singleton.mp he]
  exact hd

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_block_single

/-- **One removed dart is placed** when it is not an inner dart of `I`, and it ends `c` if it
lies on `T`. -/
theorem roseLobeChoice_place_single {I T A C : List α} {d : α} {Q : α → Prop} (hd : ¬Q d)
    (hI : d ∉ I ∨ [d] <+: I ∨ [d] <:+ I) (hT : d ∉ T ∨ C = []) :
    roseLobeRegion_Place Q I T A [d] C := by
  unfold roseLobeRegion_Place
  refine ⟨?_, ?_⟩
  · rcases hI with h | h | h
    · exact Or.inr (Or.inl ⟨d, List.mem_singleton_self d, h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases hT with h | h
    · refine Or.inl fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact h
    · refine Or.inr (Or.inl ⟨h, fun e he => ?_⟩)
      rw [List.mem_singleton.mp he]
      exact hd

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_place_single

end ChoiceLists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
