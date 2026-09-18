import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.TripleLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The three-, four- and five-dart lobe cases of the region choice

Lane gl-p10-69.  Generic (any relation `s`, any nodup walk `c`, any "kept" predicate `kp`) forms
of the lobe cases in which the union of one or more inside classes meets the walk in exactly
THREE, FOUR or FIVE consecutive darts, named explicitly:

* `roseLobeTriple_lobe_run`: `c = A ++ [a1, a2, a3] ++ C`;
* `roseLobeTriple_lobe_quad`: `c = A ++ [a1, a2, a3, a4] ++ C`;
* `roseLobeTriple_lobe_quint`: `c = A ++ [a1, a2, a3, a4, a5] ++ C`.

The witness is uniform: the lobe `rs = B` is the removed block itself (so one-, two- and
three-class lobes are one case), under the closure hypothesis "every dart of `c` in the class of
some dart of `B` is in `B`", some kept `x` in no class of `B`, reached from `c` (in use:
`roseLobeChoice_kept_on`), and the placement conditions exactly as in `roseLobeRegion_Place`.
`A ++ C ≠ []` is not assumed: it follows from the reachability of `x`.

The three lemmas have the same proof text; they are kept separate (fixed literals, no general
"run" lemma over an arbitrary block), as required.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section TripleLobe

variable {α : Type*}

/-- **Consecutive inside triple.**  Three consecutive darts of `c` closed under the classes
they meet, none of which contains the kept `x` reached from `c`, suitably placed: the lobe
`rs = [a1, a2, a3]` with the removed block `B = [a1, a2, a3]`. -/
theorem roseLobeTriple_lobe_run {s : α → α → Prop} {c I T A C : List α} {kp : α → Prop}
    {a1 a2 a3 x : α} (hnd : c.Nodup) (hc : c = A ++ [a1, a2, a3] ++ C)
    (hlone : ∀ e ∈ c, ∀ r ∈ [a1, a2, a3], Relation.EqvGen s r e → e ∈ [a1, a2, a3])
    (hx : kp x) (hax : ∀ r ∈ [a1, a2, a3], ¬Relation.EqvGen s r x)
    (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hI : (∃ d ∈ [a1, a2, a3], d ∉ I) ∨ [a1, a2, a3] <+: I ∨ [a1, a2, a3] <:+ I)
    (hT : (∀ d ∈ [a1, a2, a3], d ∉ T) ∨ C = []) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hB : ∀ d ∈ [a1, a2, a3], ¬∀ r ∈ [a1, a2, a3], ¬Relation.EqvGen s r d :=
    fun d hd h => h d hd (Relation.EqvGen.refl d)
  have hQ : ∀ e ∈ A ++ C, ∀ r ∈ [a1, a2, a3], ¬Relation.EqvGen s r e :=
    fun e he r hr hre => roseLobeTriple_not_mem_B hc hnd he
      (hlone e (roseLobeRegion_mem_AC hc he) r hr hre)
  have hne : A ++ C ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hyB : y ∉ [a1, a2, a3] := fun hyB => hax y hyB hyx
    exact List.ne_nil_of_mem (roseLobeTriple_mem_AC_of_not_mem_B hc hyc hyB)
  refine ⟨[a1, a2, a3], List.cons_ne_nil _ _, fun r hr => roseLobeRegion_mem_B hc hr,
    ⟨x, hx, hax⟩, A, [a1, a2, a3], C, ?_, ?_⟩
  · unfold roseLobeRegion_Block
    exact ⟨hc, Or.inl ⟨hB, hQ, hne⟩⟩
  · unfold roseLobeRegion_Place
    refine ⟨Or.inr hI, ?_⟩
    rcases hT with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, hB⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lobe_run

/-- **Consecutive inside quadruple.**  As `roseLobeTriple_lobe_run` for four consecutive darts:
the lobe `rs = [a1, a2, a3, a4]` with the removed block `B = [a1, a2, a3, a4]`. -/
theorem roseLobeTriple_lobe_quad {s : α → α → Prop} {c I T A C : List α} {kp : α → Prop}
    {a1 a2 a3 a4 x : α} (hnd : c.Nodup) (hc : c = A ++ [a1, a2, a3, a4] ++ C)
    (hlone : ∀ e ∈ c, ∀ r ∈ [a1, a2, a3, a4], Relation.EqvGen s r e → e ∈ [a1, a2, a3, a4])
    (hx : kp x) (hax : ∀ r ∈ [a1, a2, a3, a4], ¬Relation.EqvGen s r x)
    (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hI : (∃ d ∈ [a1, a2, a3, a4], d ∉ I) ∨ [a1, a2, a3, a4] <+: I ∨ [a1, a2, a3, a4] <:+ I)
    (hT : (∀ d ∈ [a1, a2, a3, a4], d ∉ T) ∨ C = []) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hB : ∀ d ∈ [a1, a2, a3, a4], ¬∀ r ∈ [a1, a2, a3, a4], ¬Relation.EqvGen s r d :=
    fun d hd h => h d hd (Relation.EqvGen.refl d)
  have hQ : ∀ e ∈ A ++ C, ∀ r ∈ [a1, a2, a3, a4], ¬Relation.EqvGen s r e :=
    fun e he r hr hre => roseLobeTriple_not_mem_B hc hnd he
      (hlone e (roseLobeRegion_mem_AC hc he) r hr hre)
  have hne : A ++ C ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hyB : y ∉ [a1, a2, a3, a4] := fun hyB => hax y hyB hyx
    exact List.ne_nil_of_mem (roseLobeTriple_mem_AC_of_not_mem_B hc hyc hyB)
  refine ⟨[a1, a2, a3, a4], List.cons_ne_nil _ _, fun r hr => roseLobeRegion_mem_B hc hr,
    ⟨x, hx, hax⟩, A, [a1, a2, a3, a4], C, ?_, ?_⟩
  · unfold roseLobeRegion_Block
    exact ⟨hc, Or.inl ⟨hB, hQ, hne⟩⟩
  · unfold roseLobeRegion_Place
    refine ⟨Or.inr hI, ?_⟩
    rcases hT with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, hB⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lobe_quad

/-- **Consecutive inside quintuple.**  As `roseLobeTriple_lobe_run` for five consecutive darts:
the lobe `rs = [a1, a2, a3, a4, a5]` with the removed block `B = [a1, a2, a3, a4, a5]`. -/
theorem roseLobeTriple_lobe_quint {s : α → α → Prop} {c I T A C : List α} {kp : α → Prop}
    {a1 a2 a3 a4 a5 x : α} (hnd : c.Nodup) (hc : c = A ++ [a1, a2, a3, a4, a5] ++ C)
    (hlone : ∀ e ∈ c, ∀ r ∈ [a1, a2, a3, a4, a5], Relation.EqvGen s r e →
      e ∈ [a1, a2, a3, a4, a5])
    (hx : kp x) (hax : ∀ r ∈ [a1, a2, a3, a4, a5], ¬Relation.EqvGen s r x)
    (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hI : (∃ d ∈ [a1, a2, a3, a4, a5], d ∉ I) ∨ [a1, a2, a3, a4, a5] <+: I ∨
      [a1, a2, a3, a4, a5] <:+ I)
    (hT : (∀ d ∈ [a1, a2, a3, a4, a5], d ∉ T) ∨ C = []) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hB : ∀ d ∈ [a1, a2, a3, a4, a5],
      ¬∀ r ∈ [a1, a2, a3, a4, a5], ¬Relation.EqvGen s r d :=
    fun d hd h => h d hd (Relation.EqvGen.refl d)
  have hQ : ∀ e ∈ A ++ C, ∀ r ∈ [a1, a2, a3, a4, a5], ¬Relation.EqvGen s r e :=
    fun e he r hr hre => roseLobeTriple_not_mem_B hc hnd he
      (hlone e (roseLobeRegion_mem_AC hc he) r hr hre)
  have hne : A ++ C ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hyB : y ∉ [a1, a2, a3, a4, a5] := fun hyB => hax y hyB hyx
    exact List.ne_nil_of_mem (roseLobeTriple_mem_AC_of_not_mem_B hc hyc hyB)
  refine ⟨[a1, a2, a3, a4, a5], List.cons_ne_nil _ _, fun r hr => roseLobeRegion_mem_B hc hr,
    ⟨x, hx, hax⟩, A, [a1, a2, a3, a4, a5], C, ?_, ?_⟩
  · unfold roseLobeRegion_Block
    exact ⟨hc, Or.inl ⟨hB, hQ, hne⟩⟩
  · unfold roseLobeRegion_Place
    refine ⟨Or.inr hI, ?_⟩
    rcases hT with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h, hB⟩)

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeTriple_lobe_quint

end TripleLobe

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
