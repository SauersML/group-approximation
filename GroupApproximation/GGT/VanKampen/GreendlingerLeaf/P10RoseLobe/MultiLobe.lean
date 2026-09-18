import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.MultiLists

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

end MultiLobe

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
