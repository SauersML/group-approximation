import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.ChoiceLists

/-!
# The three singleton cases of the region choice

Lane gl-p10-63.  Generic (any relation `s`, any nodup walk `c`) forms of the three cases in which
`roseLobeRegion_Statement` is witnessed by a class meeting the walk in ONE dart:

* `roseLobeChoice_lobe_in`: a dart `d` of `c` alone in its class, missing the kept face, not an
  inner dart of `I`, and ending `T` if on `T`: the lobe with `rs = [d]`, `B = [d]`.
* `roseLobeChoice_lake_out`: a dart `y` of `c` whose opposite class meets `c` only at `y` and misses
  the outer and source faces: the lake with block `B = [y]`.
* `roseLobeChoice_lobe_kept`: the kept class meets `c` in one dart `dk`, starting `T` if on `T`:
  the lobe with `rs = A ++ C` (all the other darts) and `B = [dk]` in the second colouring.

## LOUD: strength

Everything here is PROVED; there is no hypothesis Prop.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe

section ChoiceCases

variable {α : Type*}

/-- A dart of `A ++ C` is a dart of `A ++ [d] ++ C`. -/
theorem roseLobeChoice_mem_of_mem_AC {c A C : List α} {d e : α} (hc : c = A ++ [d] ++ C)
    (he : e ∈ A ++ C) : e ∈ c := by
  rw [hc]
  rcases List.mem_append.mp he with h | h
  · exact List.mem_append_left C (List.mem_append_left [d] h)
  · exact List.mem_append_right (A ++ [d]) h

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_mem_of_mem_AC

/-- **Inside singleton case.**  A dart `d` of `c` alone (on `c`) in its class, whose class misses
some `x` with `kp x` that is reached from `c`, gives the lobe `rs = [d]`, `B = [d]`. -/
theorem roseLobeChoice_lobe_in {s : α → α → Prop} {c P I T : List α} {kp : α → Prop}
    {d x : α} (hdec : c = P ++ T) (hnd : c.Nodup) (hd : d ∈ c)
    (hlone : ∀ e ∈ c, Relation.EqvGen s d e → e = d) (hx : kp x)
    (hdx : ¬Relation.EqvGen s d x) (hy : ∃ y ∈ c, Relation.EqvGen s y x)
    (hI : d ∉ I ∨ [d] <+: I ∨ [d] <:+ I) (hT : d ∉ T ∨ [d] <:+ T) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  obtain ⟨A, C, hc, hTC⟩ := roseLobeChoice_split_end hdec hd hT
  have hQd : ¬∀ r ∈ [d], ¬Relation.EqvGen s r d := fun h =>
    h d (List.mem_singleton_self d) (Relation.EqvGen.refl d)
  have hQ : ∀ e ∈ A ++ C, ∀ r ∈ [d], ¬Relation.EqvGen s r e := by
    intro e he r hr hre
    rw [List.mem_singleton.mp hr] at hre
    exact roseLobeChoice_ne_of_mem hc hnd he (hlone e (roseLobeChoice_mem_of_mem_AC hc he) hre)
  have hne : A ++ C ≠ [] := by
    obtain ⟨y, hyc, hyx⟩ := hy
    have hyd : y ≠ d := by
      intro h
      rw [h] at hyx
      exact hdx hyx
    exact List.ne_nil_of_mem (roseLobeChoice_mem_AC_of_ne hc hyc hyd)
  refine ⟨[d], List.cons_ne_nil d [], fun r hr => ?_, ⟨x, hx, fun r hr => ?_⟩, A, [d], C,
    roseLobeChoice_block_single hc hne hQd hQ, roseLobeChoice_place_single hQd hI hTC⟩
  · rw [List.mem_singleton.mp hr]
    exact hd
  · rw [List.mem_singleton.mp hr]
    exact hdx

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_lobe_in

/-- **Outside singleton case.**  A dart `y` of `c` such that no other `e ∈ c` has `f e` in the
class of `f y` (in use `f = alpha`), and that class misses `PO`, `PS`: the lake with
`B = [y]`. -/
theorem roseLobeChoice_lake_out {s : α → α → Prop} {c : List α} {f : α → α}
    {PO PS : α → Prop} {y : α} (hnd : c.Nodup) (hy : y ∈ c)
    (hlone : ∀ e ∈ c, Relation.EqvGen s (f y) (f e) → e = y)
    (hO : ∀ x, PO x → ¬Relation.EqvGen s (f y) x) (hS : ∀ x, PS x → ¬Relation.EqvGen s (f y) x)
    (hoth : ∃ e ∈ c, e ≠ y) :
    ∃ y ∈ c, (∀ x, PO x → ¬Relation.EqvGen s (f y) x) ∧
      (∀ x, PS x → ¬Relation.EqvGen s (f y) x) ∧
      ∃ A B C : List α, roseLobeRegion_Block c (fun d => ¬Relation.EqvGen s (f y) (f d)) A B C := by
  obtain ⟨A, C, h⟩ := List.append_of_mem hy
  have hc : c = A ++ [y] ++ C := by
    rw [h]
    simp
  have hQy : ¬¬Relation.EqvGen s (f y) (f y) := fun h => h (Relation.EqvGen.refl (f y))
  have hQ : ∀ e ∈ A ++ C, ¬Relation.EqvGen s (f y) (f e) := by
    intro e he hre
    exact roseLobeChoice_ne_of_mem hc hnd he (hlone e (roseLobeChoice_mem_of_mem_AC hc he) hre)
  have hne : A ++ C ≠ [] := by
    obtain ⟨e, hec, hey⟩ := hoth
    exact List.ne_nil_of_mem (roseLobeChoice_mem_AC_of_ne hc hec hey)
  exact ⟨y, hy, hO, hS, A, [y], C, roseLobeChoice_block_single hc hne hQy hQ⟩

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_lake_out

/-- **Kept singleton case.**  The class of `x` (with `kp x`) meets `c` in the one dart `dk`, which
starts `T` if it lies on `T`: the lobe with `rs = A ++ C` (every other dart) and `B = [dk]`,
coloured the second way (`Q` true on `B`, false on `A ++ C`). -/
theorem roseLobeChoice_lobe_kept {s : α → α → Prop} {c P I T : List α} {kp : α → Prop}
    {x dk : α} (hdec : c = P ++ T) (hnd : c.Nodup) (hx : kp x) (hdk : dk ∈ c)
    (hdkx : Relation.EqvGen s dk x) (hlone : ∀ e ∈ c, Relation.EqvGen s dk e → e = dk)
    (hoth : ∃ e ∈ c, e ≠ dk) (hT : dk ∉ T ∨ [dk] <+: T) :
    ∃ rs : List α, rs ≠ [] ∧ (∀ r ∈ rs, r ∈ c) ∧
      (∃ x, kp x ∧ ∀ r ∈ rs, ¬Relation.EqvGen s r x) ∧
      ∃ A B C : List α,
        roseLobeRegion_Block c (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) A B C ∧
        roseLobeRegion_Place (fun e => ∀ r ∈ rs, ¬Relation.EqvGen s r e) I T A B C := by
  obtain ⟨A, C, hc, hTA⟩ := roseLobeChoice_split_start hdec hnd hdk hT
  have hr : ∀ r ∈ A ++ C, ¬Relation.EqvGen s dk r := fun r hr h =>
    roseLobeChoice_ne_of_mem hc hnd hr (hlone r (roseLobeChoice_mem_of_mem_AC hc hr) h)
  have hne : A ++ C ≠ [] := by
    obtain ⟨e, hec, hed⟩ := hoth
    exact List.ne_nil_of_mem (roseLobeChoice_mem_AC_of_ne hc hec hed)
  have hnotQ : ∀ e ∈ A ++ C, ¬∀ r ∈ A ++ C, ¬Relation.EqvGen s r e := fun e he h =>
    h e he (Relation.EqvGen.refl e)
  have hQdk : ∀ e ∈ [dk], ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e := by
    intro e he r hrm h
    rw [List.mem_singleton.mp he] at h
    exact hr r hrm (Relation.EqvGen.symm r dk h)
  have hblock : roseLobeRegion_Block c (fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e)
      A [dk] C := by
    unfold roseLobeRegion_Block
    exact ⟨hc, Or.inr ⟨hQdk, hnotQ, List.cons_ne_nil dk []⟩⟩
  have hplace : roseLobeRegion_Place (fun e => ∀ r ∈ A ++ C, ¬Relation.EqvGen s r e)
      I T A [dk] C := by
    unfold roseLobeRegion_Place
    refine ⟨Or.inl hnotQ, ?_⟩
    rcases hTA with h | h
    · refine Or.inl fun e he => ?_
      rw [List.mem_singleton.mp he]
      exact h
    · exact Or.inr (Or.inr ⟨hnotQ, h⟩)
  refine ⟨A ++ C, hne, fun r hrm => roseLobeChoice_mem_of_mem_AC hc hrm,
    ⟨x, hx, fun r hrm h => ?_⟩, A, [dk], C, hblock, hplace⟩
  exact hr r hrm (Relation.EqvGen.trans dk x r hdkx (Relation.EqvGen.symm r x h))

#audit_axioms
  GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe.roseLobeChoice_lobe_kept

end ChoiceCases

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10RoseLobe
