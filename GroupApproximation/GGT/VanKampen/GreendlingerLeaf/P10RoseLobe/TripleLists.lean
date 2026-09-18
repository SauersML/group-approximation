import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLists
import GroupApproximation.Meta.AxiomGuard

/-!
# List facts for the three-, four- and five-dart cases

Lane gl-p10-69.  Plain list facts used by `TripleLake` and `TripleLobe`: in a nodup
`c = A ++ B ++ C` the parts `A ++ C` and `B` are disjoint, a dart of `c` off `B` lies in
`A ++ C`, and a property of three named darts holds on their literal list.  These are facts
about an arbitrary split `A ++ B ++ C`; they say nothing about face classes, so they are not a
"run lemma" (every case lemma built on them fixes the removed darts as an explicit literal).

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section TripleLists

variable {α : Type*}

/-- In a nodup list `A ++ B ++ C`, a dart of `A ++ C` is not a dart of `B`. -/
theorem roseLobeTriple_not_mem_B {c A B C : List α} {e : α} (hc : c = A ++ B ++ C)
    (hnd : c.Nodup) (he : e ∈ A ++ C) : e ∉ B := by
  intro heB
  rw [hc] at hnd
  have h1 := List.nodup_append.mp hnd
  rcases List.mem_append.mp he with h | h
  · exact (List.nodup_append.mp h1.1).2.2 e h e heB rfl
  · exact h1.2.2 e (List.mem_append_right A heB) e h rfl

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_not_mem_B

/-- A dart of `A ++ B ++ C` that is not a dart of `B` is a dart of `A ++ C`. -/
theorem roseLobeTriple_mem_AC_of_not_mem_B {c A B C : List α} {e : α} (hc : c = A ++ B ++ C)
    (he : e ∈ c) (hB : e ∉ B) : e ∈ A ++ C := by
  rw [hc] at he
  rcases List.mem_append.mp he with h | h
  · rcases List.mem_append.mp h with h | h
    · exact List.mem_append_left C h
    · exact absurd h hB
  · exact List.mem_append_right A h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_mem_AC_of_not_mem_B

/-- A property of `a1`, `a2` and `a3` holds on `[a1, a2, a3]`. -/
theorem roseLobeTriple_forall_three {P : α → Prop} {a1 a2 a3 : α} (h1 : P a1) (h2 : P a2)
    (h3 : P a3) : ∀ d ∈ [a1, a2, a3], P d := by
  intro d hd
  rcases List.mem_cons.mp hd with h | h
  · rw [h]
    exact h1
  · exact roseLobeMulti_forall_pair (P := P) h2 h3 d h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_forall_three

end TripleLists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
