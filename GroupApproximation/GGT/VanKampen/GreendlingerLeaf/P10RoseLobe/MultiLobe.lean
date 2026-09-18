import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLists
import GroupApproximation.Meta.AxiomGuard

/-!
# The two-dart lobe cases of the region choice

Lane gl-p10-67.  Generic (any relation `s`, any nodup walk `c`, any "kept" predicate `kp`) forms
of the three lobe cases in which a region meets the walk from inside in exactly TWO darts `a`,
`b`, cyclically adjacent on `c`:

* `roseLobeMulti_lobe_pair`: `c = A ++ [a, b] ++ C`, the class of `a` meets `c` in `{a, b}` and
  misses some kept `x` reached from `c`: the lobe `rs = [a]`, block `B = [a, b]` removed;
* `roseLobeMulti_lobe_wrap`: the same with `c = [a] ++ M ++ [b]`: the lobe `rs = [a]`, block
  `B = M` kept, the two ends removed;
* `roseLobeMulti_kept_pair`: the kept class meets `c` in `{a, b}`, `c = A ++ [a, b] ++ C`, and
  `A ++ C ≠ []`: the lobe `rs = A ++ C`, block `B = [a, b]` kept.

The placement side conditions (`hI`, `hT`) are exactly those under which the lemmas of
`MultiLists` give `roseLobeRegion_Place`.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section MultiLobe

variable {α : Type*}

/-- **Adjacent inside pair.**  Two consecutive darts `a`, `b` of `c` forming the whole trace on
`c` of the class of `a`, which misses some kept `x` reached from `c`: the lobe `rs = [a]` with
the removed block `B = [a, b]`. -/
theorem roseLobeMulti_lobe_pair {s : α → α → Prop} {c I T A C : List α} {kp : α → Prop}
    {a b x : α} (hnd : c.Nodup) (hc : c = A ++ [a, b] ++ C) (hab : Relation.EqvGen s a b)
    (hlone : ∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b) (hx : kp x)
    (hax : ¬Relation.EqvGen s a x) (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hI : a ∉ I ∨ b ∉ I ∨ [a, b] <+: I ∨ [a, b] <:+ I) (hT : (a ∉ T ∧ b ∉ T) ∨ C = []) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hQa : ¬∀ r ∈ [a], ¬Relation.EqvGen s r a := fun h =>
    h a (List.mem_singleton_self a) (Relation.EqvGen.refl a)
  have hQb : ¬∀ r ∈ [a], ¬Relation.EqvGen s r b := fun h =>
    h a (List.mem_singleton_self a) hab
  have hQ : ∀ e ∈ A ++ C, ∀ r ∈ [a], ¬Relation.EqvGen s r e := by
    intro e he r hr hre
    rw [List.mem_singleton.mp hr] at hre
    have hea := roseLobeMulti_ne_of_mem_pair hc hnd he
    rcases hlone e (roseLobeMulti_mem_of_mem_AC_pair hc he) hre with h | h
    · exact hea.1 h
    · exact hea.2 h
  have hne : A ++ C ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hya : y ≠ a := by
      intro h
      rw [h] at hyx
      exact hax hyx
    have hyb : y ≠ b := by
      intro h
      rw [h] at hyx
      exact hax (Relation.EqvGen.trans a b x hab hyx)
    exact List.ne_nil_of_mem (roseLobeMulti_mem_AC_of_ne_pair hc hyc hya hyb)
  refine ⟨[a], List.cons_ne_nil a [], fun r hr => ?_, ⟨x, hx, fun r hr => ?_⟩, A, [a, b], C,
    roseLobeMulti_block_pair (Q := fun e => ∀ r ∈ [a], ¬Relation.EqvGen s r e)
      hc hne hQa hQb hQ,
    roseLobeMulti_place_pair (Q := fun e => ∀ r ∈ [a], ¬Relation.EqvGen s r e)
      hQa hQb hI hT⟩
  · rw [List.mem_singleton.mp hr]
    exact roseLobeMulti_mem_left_pair hc
  · rw [List.mem_singleton.mp hr]
    exact hax

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_lobe_pair

/-- **Inside pair at the ends.**  The first dart `a` and the last dart `b` of `c` forming the
whole trace on `c` of the class of `a`, which misses some kept `x` reached from `c`: the lobe
`rs = [a]` with the kept block `B = M`. -/
theorem roseLobeMulti_lobe_wrap {s : α → α → Prop} {c I T M : List α} {kp : α → Prop}
    {a b x : α} (hnd : c.Nodup) (hc : c = [a] ++ M ++ [b]) (hab : Relation.EqvGen s a b)
    (hlone : ∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b) (hx : kp x)
    (hax : ¬Relation.EqvGen s a x) (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hT : (∀ d ∈ M, d ∉ T) ∨ a ∉ T) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hQa : ¬∀ r ∈ [a], ¬Relation.EqvGen s r a := fun h =>
    h a (List.mem_singleton_self a) (Relation.EqvGen.refl a)
  have hQb : ¬∀ r ∈ [a], ¬Relation.EqvGen s r b := fun h =>
    h a (List.mem_singleton_self a) hab
  have hQ : ∀ e ∈ M, ∀ r ∈ [a], ¬Relation.EqvGen s r e := by
    intro e he r hr hre
    rw [List.mem_singleton.mp hr] at hre
    have hea := roseLobeMulti_ne_of_mem_wrap hc hnd he
    rcases hlone e (roseLobeMulti_mem_of_mem_wrap hc he) hre with h | h
    · exact hea.1 h
    · exact hea.2 h
  have hM : M ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hya : y ≠ a := by
      intro h
      rw [h] at hyx
      exact hax hyx
    have hyb : y ≠ b := by
      intro h
      rw [h] at hyx
      exact hax (Relation.EqvGen.trans a b x hab hyx)
    exact List.ne_nil_of_mem (roseLobeMulti_mem_M_of_ne_wrap hc hyc hya hyb)
  have hAC : ∀ d ∈ [a] ++ [b], ¬∀ r ∈ [a], ¬Relation.EqvGen s r d := by
    intro d hd
    rcases List.mem_append.mp hd with h | h
    · rw [List.mem_singleton.mp h]
      exact hQa
    · rw [List.mem_singleton.mp h]
      exact hQb
  refine ⟨[a], List.cons_ne_nil a [], fun r hr => ?_, ⟨x, hx, fun r hr => ?_⟩, [a], M, [b],
    roseLobeMulti_block_wrap (Q := fun e => ∀ r ∈ [a], ¬Relation.EqvGen s r e)
      hc hM hQa hQb hQ,
    roseLobeMulti_place_wrap (Q := fun e => ∀ r ∈ [a], ¬Relation.EqvGen s r e) hAC hT⟩
  · rw [List.mem_singleton.mp hr]
    exact roseLobeMulti_mem_left_wrap hc
  · rw [List.mem_singleton.mp hr]
    exact hax

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_lobe_wrap

/-- **Kept pair.**  The class of a kept `x` meets `c` in the two consecutive darts `a`, `b` of
`c = A ++ [a, b] ++ C`, `A ++ C ≠ []`, and the pair misses `T` or nothing of `A` is on `T`: the
lobe `rs = A ++ C` with the kept block `B = [a, b]`. -/
theorem roseLobeMulti_kept_pair {s : α → α → Prop} {c I T A C : List α} {kp : α → Prop}
    {a b x : α} (hnd : c.Nodup) (hc : c = A ++ [a, b] ++ C) (hne : A ++ C ≠ []) (hx : kp x)
    (hax : Relation.EqvGen s a x) (hab : Relation.EqvGen s a b)
    (hlone : ∀ e ∈ c, Relation.EqvGen s a e → e = a ∨ e = b)
    (hT : (a ∉ T ∧ b ∉ T) ∨ ∀ e ∈ A, e ∉ T) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  have hr : ∀ r ∈ A ++ C, ¬Relation.EqvGen s a r := by
    intro r hrm h
    have hra := roseLobeMulti_ne_of_mem_pair hc hnd hrm
    rcases hlone r (roseLobeMulti_mem_of_mem_AC_pair hc hrm) h with h' | h'
    · exact hra.1 h'
    · exact hra.2 h'
  have hnotQ : ∀ e ∈ A ++ C, ¬∀ r ∈ A ++ C, ¬Relation.EqvGen s r e := fun e he h =>
    h e he (Relation.EqvGen.refl e)
  have hQab : ∀ e ∈ [a, b], ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e :=
    roseLobeMulti_forall_pair (P := fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e)
      (fun r hrm h => hr r hrm (Relation.EqvGen.symm r a h))
      (fun r hrm h => hr r hrm (Relation.EqvGen.trans a b r hab (Relation.EqvGen.symm r b h)))
  have hblock : roseLobeRegion_Block c (fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e)
      A [a, b] C := by
    unfold roseLobeRegion_Block
    exact ⟨hc, Or.inr ⟨hQab, hnotQ, List.cons_ne_nil a [b]⟩⟩
  have hplace : roseLobeRegion_Place (fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e)
      I T A [a, b] C :=
    roseLobeMulti_place_keptPair (Q := fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e) hnotQ hT
  refine ⟨A ++ C, hne, fun r hrm => roseLobeMulti_mem_of_mem_AC_pair hc hrm,
    ⟨x, hx, fun r hrm h => ?_⟩, A, [a, b], C, hblock, hplace⟩
  exact hr r hrm (Relation.EqvGen.trans a x r hax (Relation.EqvGen.symm r x h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeMulti_kept_pair

end MultiLobe

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
