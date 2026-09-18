import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.ChoiceCases
import GroupApproximation.Meta.AxiomGuard

/-!
# Two removed darts: block and placement

Lane gl-p10-67.  List facts for the two-dart cases of `roseLobeChoice_Statement`.  A region
meeting the nodup walk `c` in exactly two darts `a`, `b` that are cyclically adjacent on `c`
comes in two shapes:

* (pair) `c = A ++ [a, b] ++ C`: the block `B = [a, b]`, removed (`roseLobeMulti_block_pair`);
* (wrap) `c = [a] ++ M ++ [b]` (`a` first, `b` last): the block `B = M`, kept, with
  `A ++ C = [a] ++ [b]` removed (`roseLobeMulti_block_wrap`).

The placement clause `roseLobeRegion_Place` for these blocks is `roseLobeMulti_place_pair`
(removed pair), `roseLobeMulti_place_keptPair` (kept pair, the rest removed) and
`roseLobeMulti_place_wrap` (removed ends).

No contiguity is assumed anywhere: the two darts are given with their positions, exactly as the
single dart of gl-p10-63's `ChoiceLists`.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section MultiLists

variable {α : Type*}

/-- A property of both `a` and `b` holds on `[a, b]`. -/
theorem roseLobeMulti_forall_pair {P : α → Prop} {a b : α} (ha : P a) (hb : P b) :
    ∀ d ∈ [a, b], P d := by
  intro d hd
  rcases List.mem_cons.mp hd with h | h
  · rw [h]
    exact ha
  · rw [List.mem_singleton.mp h]
    exact hb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_forall_pair

/-- A dart of `A ++ C` is a dart of `A ++ [a, b] ++ C`. -/
theorem roseLobeMulti_mem_of_mem_AC_pair {c A C : List α} {a b e : α}
    (hc : c = A ++ [a, b] ++ C) (he : e ∈ A ++ C) : e ∈ c := by
  rw [hc]
  rcases List.mem_append.mp he with h | h
  · exact List.mem_append_left C (List.mem_append_left [a, b] h)
  · exact List.mem_append_right (A ++ [a, b]) h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_of_mem_AC_pair

/-- The first dart of the pair is a dart of `A ++ [a, b] ++ C`. -/
theorem roseLobeMulti_mem_left_pair {c A C : List α} {a b : α} (hc : c = A ++ [a, b] ++ C) :
    a ∈ c := by
  rw [hc]
  exact List.mem_append_left C (List.mem_append_right A List.mem_cons_self)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_left_pair

/-- In a nodup list `A ++ [a, b] ++ C`, a dart of `A ++ C` is neither `a` nor `b`. -/
theorem roseLobeMulti_ne_of_mem_pair {c A C : List α} {a b e : α} (hc : c = A ++ [a, b] ++ C)
    (hnd : c.Nodup) (he : e ∈ A ++ C) : e ≠ a ∧ e ≠ b := by
  have h1 : c = A ++ [a] ++ ([b] ++ C) := by
    simp [hc]
  have h2 : c = A ++ [a] ++ [b] ++ C := by
    simp [hc]
  refine ⟨roseLobeChoice_ne_of_mem h1 hnd ?_, roseLobeChoice_ne_of_mem h2 hnd ?_⟩
  · rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left ([b] ++ C) h
    · exact List.mem_append_right A (List.mem_append_right [b] h)
  · rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left C (List.mem_append_left [a] h)
    · exact List.mem_append_right (A ++ [a]) h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_ne_of_mem_pair

/-- A dart of `A ++ [a, b] ++ C` other than `a` and `b` lies in `A ++ C`. -/
theorem roseLobeMulti_mem_AC_of_ne_pair {c A C : List α} {a b e : α}
    (hc : c = A ++ [a, b] ++ C) (he : e ∈ c) (ha : e ≠ a) (hb : e ≠ b) : e ∈ A ++ C := by
  rw [hc] at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left C h
    · rcases List.mem_cons.mp h with h | h
      · exact absurd h ha
      · exact absurd (List.mem_singleton.mp h) hb
  · exact List.mem_append_right A h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_AC_of_ne_pair

/-- A dart of `M` is a dart of `[a] ++ M ++ [b]`. -/
theorem roseLobeMulti_mem_of_mem_wrap {c M : List α} {a b e : α} (hc : c = [a] ++ M ++ [b])
    (he : e ∈ M) : e ∈ c := by
  rw [hc]
  exact List.mem_append_left [b] (List.mem_append_right [a] he)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_of_mem_wrap

/-- The first dart `a` is a dart of `[a] ++ M ++ [b]`. -/
theorem roseLobeMulti_mem_left_wrap {c M : List α} {a b : α} (hc : c = [a] ++ M ++ [b]) :
    a ∈ c := by
  rw [hc]
  exact List.mem_append_left [b] (List.mem_append_left M (List.mem_singleton_self a))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_left_wrap

/-- In a nodup list `[a] ++ M ++ [b]`, a dart of `M` is neither `a` nor `b`. -/
theorem roseLobeMulti_ne_of_mem_wrap {c M : List α} {a b e : α} (hc : c = [a] ++ M ++ [b])
    (hnd : c.Nodup) (he : e ∈ M) : e ≠ a ∧ e ≠ b := by
  have h1 : c = [] ++ [a] ++ (M ++ [b]) := by
    simp [hc]
  have h2 : c = ([a] ++ M) ++ [b] ++ [] := by
    simp [hc]
  exact ⟨roseLobeChoice_ne_of_mem h1 hnd
      (List.mem_append_right [] (List.mem_append_left [b] he)),
    roseLobeChoice_ne_of_mem h2 hnd (List.mem_append_left [] (List.mem_append_right [a] he))⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_ne_of_mem_wrap

/-- A dart of `[a] ++ M ++ [b]` other than `a` and `b` lies in `M`. -/
theorem roseLobeMulti_mem_M_of_ne_wrap {c M : List α} {a b e : α} (hc : c = [a] ++ M ++ [b])
    (he : e ∈ c) (ha : e ≠ a) (hb : e ≠ b) : e ∈ M := by
  rw [hc] at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h | h
    · exact absurd (List.mem_singleton.mp h) ha
    · exact h
  · exact absurd (List.mem_singleton.mp h) hb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_mem_M_of_ne_wrap

/-- **Two adjacent removed darts are a block**: `Q` false at `a`, `b`, true on the nonempty
rest `A ++ C`. -/
theorem roseLobeMulti_block_pair {c A C : List α} {a b : α} {Q : α → Prop}
    (hc : c = A ++ [a, b] ++ C) (hne : A ++ C ≠ []) (ha : ¬Q a) (hb : ¬Q b)
    (hQ : ∀ e ∈ A ++ C, Q e) : roseLobeRegion_Block c Q A [a, b] C := by
  unfold roseLobeRegion_Block
  exact ⟨hc, Or.inl ⟨roseLobeMulti_forall_pair (P := fun d => ¬Q d) ha hb, hQ, hne⟩⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_block_pair

/-- **Two removed end darts are a block**: `c = [a] ++ M ++ [b]`, `Q` false at `a`, `b`, true
on the nonempty middle `M` (the second colouring: `B = M` kept, `A ++ C = [a] ++ [b]`
removed). -/
theorem roseLobeMulti_block_wrap {c M : List α} {a b : α} {Q : α → Prop}
    (hc : c = [a] ++ M ++ [b]) (hM : M ≠ []) (ha : ¬Q a) (hb : ¬Q b) (hQ : ∀ e ∈ M, Q e) :
    roseLobeRegion_Block c Q [a] M [b] := by
  unfold roseLobeRegion_Block
  refine ⟨hc, Or.inr ⟨hQ, ?_, hM⟩⟩
  intro e he
  rcases List.mem_append.mp he with h | h
  · rw [List.mem_singleton.mp h]
    exact ha
  · rw [List.mem_singleton.mp h]
    exact hb

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_block_wrap

/-- **A removed pair is placed** when it is not inside `I` away from both ends of `I`, and it
ends `c` if it meets `T`. -/
theorem roseLobeMulti_place_pair {I T A C : List α} {a b : α} {Q : α → Prop} (ha : ¬Q a)
    (hb : ¬Q b) (hI : a ∉ I ∨ b ∉ I ∨ [a, b] <+: I ∨ [a, b] <:+ I)
    (hT : (a ∉ T ∧ b ∉ T) ∨ C = []) : roseLobeRegion_Place Q I T A [a, b] C := by
  unfold roseLobeRegion_Place
  refine ⟨?_, ?_⟩
  · rcases hI with h | h | h | h
    · exact Or.inr (Or.inl ⟨a, List.mem_cons_self, h⟩)
    · exact Or.inr (Or.inl ⟨b, List.mem_cons.mpr (Or.inr (List.mem_singleton_self b)), h⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rcases hT with ⟨h1, h2⟩ | h
    · exact Or.inl (roseLobeMulti_forall_pair (P := fun d => d ∉ T) h1 h2)
    · exact Or.inr (Or.inl ⟨h, roseLobeMulti_forall_pair (P := fun d => ¬Q d) ha hb⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_place_pair

/-- **A kept pair is placed** (everything else removed) when it misses `T`, or nothing of `T`
comes before it. -/
theorem roseLobeMulti_place_keptPair {I T A C : List α} {a b : α} {Q : α → Prop}
    (hAC : ∀ d ∈ A ++ C, ¬Q d) (hT : (a ∉ T ∧ b ∉ T) ∨ ∀ e ∈ A, e ∉ T) :
    roseLobeRegion_Place Q I T A [a, b] C := by
  unfold roseLobeRegion_Place
  refine ⟨Or.inl hAC, ?_⟩
  rcases hT with ⟨h1, h2⟩ | h
  · exact Or.inl (roseLobeMulti_forall_pair (P := fun d => d ∉ T) h1 h2)
  · exact Or.inr (Or.inr ⟨hAC, h⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_place_keptPair

/-- **Removed end darts are placed** (the middle `M` kept) when `M` misses `T` or the first
dart `a` is off `T`. -/
theorem roseLobeMulti_place_wrap {I T M : List α} {a b : α} {Q : α → Prop}
    (hAC : ∀ d ∈ [a] ++ [b], ¬Q d) (hT : (∀ d ∈ M, d ∉ T) ∨ a ∉ T) :
    roseLobeRegion_Place Q I T [a] M [b] := by
  unfold roseLobeRegion_Place
  refine ⟨Or.inl hAC, ?_⟩
  rcases hT with h | h
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨hAC, fun d hd => ?_⟩)
    rw [List.mem_singleton.mp hd]
    exact h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_place_wrap

end MultiLists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
