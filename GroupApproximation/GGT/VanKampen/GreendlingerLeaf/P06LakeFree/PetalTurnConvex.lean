import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurnList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: convexity of the pieces of a cut sublist (lane gl-p06-18)

List combinatorics for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The mathematical proof

Throughout `T` has no repeated entry, `L <+ T`, `t <:+: T`, `L` is convex in `t`
(`OrderCactus.RunConvex L t`) and `L = u ++ B ++ v`.  Write `x ≺ y` for `[x, y] <+ T`.

1. *The middle piece* (`runConvex_middle`).  `B` is convex in `t`.  Let `t = U ++ y :: V` with
   `y ∉ B`.  If `y ∉ L`, convexity of `L` applies.  If `y ∈ u`, an entry of `U` on `B` would come
   before `y` on `t` and after `y` on `L`: antisymmetry.  Likewise for `y ∈ v` and `V`.
2. *The outer pieces* (`runConvex_outer`).  If `u ++ v` is not convex in `t`, then both junctions
   of `B` are adjacent on `t`.  Take `t = U ++ y :: V`, `y ∉ u ++ v`, `e₁ ∈ U` and `e₂ ∈ V` on
   `u ++ v`.  Convexity of `L` forces `y ∈ L`, so `y ∈ B`.  By antisymmetry `e₁ ∈ u` (an entry
   of `v` comes after `y` on `L`) and `e₂ ∈ v`.  The last entry `x₁` of `u` satisfies
   `e₁ ⪯ x₁ ≺ y`, the first entry `z₁` of `B` satisfies `e₁ ≺ z₁ ⪯ y`, the last entry `x₂` of `B`
   satisfies `y ⪯ x₂ ≺ e₂`, and the first entry `z₂` of `v` satisfies `y ≺ z₂ ⪯ e₂`; by
   betweenness all four lie on `t`, and the adjacency lemma makes `x₁ :: z₁` and `x₂ :: z₂`
   infixes of `t`.

Truth check: in item 2 both junctions are needed.  With `T = t = [a, b, c]`, `L = [a, b, c]`,
`u = [a]`, `B = [b]`, `v = [c]`, both junctions are adjacent and `u ++ v = [a, c]` is not convex;
with `B = []` (excluded by `y ∈ B`) nothing is cut.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

variable {α : Type*}

/-- Betweenness, allowing the ends to coincide with the middle entry. -/
theorem mem_of_between_or_eq {T t : List α} {a b c : α} (hnd : T.Nodup) (ht : t <:+: T)
    (ha : a ∈ t) (hc : c ∈ t) (hab : a = b ∨ [a, b] <+ T) (hbc : b = c ∨ [b, c] <+ T) :
    b ∈ t := by
  rcases hab with rfl | hab
  · exact ha
  · rcases hbc with rfl | hbc
    · exact hc
    · exact mem_of_between hnd ht ha hc hab hbc

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.mem_of_between_or_eq

/-- Every entry of a list is its last entry or comes before it. -/
theorem eq_or_pair_sublist_of_concat {T u u' : List α} {e x : α} (hu : u = u' ++ [x])
    (he : e ∈ u) (huT : u <+ T) : e = x ∨ [e, x] <+ T := by
  subst hu
  rcases List.mem_append.mp he with he | he
  · exact Or.inr ((pair_sublist_append he (List.mem_singleton_self x)).trans huT)
  · exact Or.inl (List.mem_singleton.mp he)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.eq_or_pair_sublist_of_concat

/-- Every entry of a list is its first entry or comes after it. -/
theorem eq_or_pair_sublist_of_cons {T B B' : List α} {e z : α} (hB : B = z :: B')
    (he : e ∈ B) (hBT : B <+ T) : z = e ∨ [z, e] <+ T := by
  subst hB
  rcases List.mem_cons.mp he with he | he
  · exact Or.inl he.symm
  · exact Or.inr ((List.cons_sublist_cons.mpr (List.singleton_sublist.mpr he)).trans hBT)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.eq_or_pair_sublist_of_cons

/-- **The middle piece of a convex sublist is convex.** -/
theorem runConvex_middle {T L t u B v : List α} (hnd : T.Nodup) (hLT : L <+ T)
    (ht : t <:+: T) (hconv : OrderCactus.RunConvex L t) (hL : L = u ++ B ++ v) :
    OrderCactus.RunConvex B t := by
  intro U y V hU hyB
  have htT : t <+ T := ht.sublist
  by_cases hyL : y ∈ L
  · rw [hL] at hyL
    rcases List.mem_append.mp hyL with hyL | hyv
    · rcases List.mem_append.mp hyL with hyu | hyB'
      · refine Or.inl fun e heU heB => pair_sublist_antisymm (x := e) (y := y) hnd ?_ ?_
        · exact (show [e, y] <+ t by
            rw [hU]
            exact pair_sublist_append heU List.mem_cons_self).trans htT
        · refine List.Sublist.trans ?_ hLT
          rw [hL, List.append_assoc]
          exact pair_sublist_append hyu (List.mem_append_left v heB)
      · exact (hyB hyB').elim
    · refine Or.inr fun e heV heB => pair_sublist_antisymm (x := y) (y := e) hnd ?_ ?_
      · exact (pair_sublist_of_eq hU heV).trans htT
      · refine List.Sublist.trans ?_ hLT
        rw [hL]
        exact pair_sublist_append (List.mem_append_right u heB) hyv
  · have hBL : ∀ e ∈ B, e ∈ L := fun e he => by
      rw [hL]
      exact List.mem_append_left v (List.mem_append_right u he)
    rcases hconv U y V hU hyL with h | h
    · exact Or.inl fun e he heB => h e he (hBL e heB)
    · exact Or.inr fun e he heB => h e he (hBL e heB)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.runConvex_middle

/-- **The outer pieces of a convex sublist are convex, unless both junctions are adjacent.** -/
theorem runConvex_outer {T L t u B v : List α} (hnd : T.Nodup) (hLT : L <+ T)
    (ht : t <:+: T) (hconv : OrderCactus.RunConvex L t) (hL : L = u ++ B ++ v)
    (hbad : ¬ ((∃ x ∈ u.getLast?, ∃ z ∈ B.head?, ∃ p q, t = p ++ x :: z :: q) ∧
      (∃ x ∈ B.getLast?, ∃ z ∈ v.head?, ∃ p q, t = p ++ x :: z :: q))) :
    OrderCactus.RunConvex (u ++ v) t := by
  intro U y V hU hyuv
  have htT : t <+ T := ht.sublist
  by_contra hne
  obtain ⟨hne₁, hne₂⟩ := not_or.mp hne
  obtain ⟨e₁, he₁U, he₁⟩ : ∃ e ∈ U, e ∈ u ++ v := by
    by_contra h
    exact hne₁ fun e he hl => h ⟨e, he, hl⟩
  obtain ⟨e₂, he₂V, he₂⟩ : ∃ e ∈ V, e ∈ u ++ v := by
    by_contra h
    exact hne₂ fun e he hl => h ⟨e, he, hl⟩
  have hi : ∀ {e f : α}, e ∈ u → f ∈ B → [e, f] <+ T := fun he hf => by
    refine List.Sublist.trans ?_ hLT
    rw [hL, List.append_assoc]
    exact pair_sublist_append he (List.mem_append_left v hf)
  have hii : ∀ {e f : α}, e ∈ B → f ∈ v → [e, f] <+ T := fun he hf => by
    refine List.Sublist.trans ?_ hLT
    rw [hL]
    exact pair_sublist_append (List.mem_append_right u he) hf
  have huvL : ∀ e ∈ u ++ v, e ∈ L := fun e he => by
    rw [hL]
    rcases List.mem_append.mp he with h | h
    · exact List.mem_append_left v (List.mem_append_left B h)
    · exact List.mem_append_right _ h
  have he₁t : [e₁, y] <+ T := (show [e₁, y] <+ t by
    rw [hU]
    exact pair_sublist_append he₁U List.mem_cons_self).trans htT
  have he₂t : [y, e₂] <+ T := (pair_sublist_of_eq hU he₂V).trans htT
  have hyL : y ∈ L := by
    by_contra hyL
    rcases hconv U y V hU hyL with h | h
    · exact h e₁ he₁U (huvL e₁ he₁)
    · exact h e₂ he₂V (huvL e₂ he₂)
  have hyB : y ∈ B := by
    rw [hL] at hyL
    rcases List.mem_append.mp hyL with h | h
    · rcases List.mem_append.mp h with h | h
      · exact (hyuv (List.mem_append_left v h)).elim
      · exact h
    · exact (hyuv (List.mem_append_right u h)).elim
  have he₁u : e₁ ∈ u := by
    rcases List.mem_append.mp he₁ with h | h
    · exact h
    · exact (pair_sublist_antisymm hnd he₁t (hii hyB h)).elim
  have he₂v : e₂ ∈ v := by
    rcases List.mem_append.mp he₂ with h | h
    · exact (pair_sublist_antisymm hnd he₂t (hi h hyB)).elim
    · exact h
  have he₁m : e₁ ∈ t := by
    rw [hU]
    exact List.mem_append_left _ he₁U
  have hym : y ∈ t := by
    rw [hU]
    exact List.mem_append_right U List.mem_cons_self
  have he₂m : e₂ ∈ t := by
    rw [hU]
    exact List.mem_append_right U (List.mem_cons_of_mem y he₂V)
  have huL : u <+ T := by
    refine List.Sublist.trans ?_ hLT
    rw [hL]
    exact (List.sublist_append_left u B).trans (List.sublist_append_left _ v)
  have hBL : B <+ T := by
    refine List.Sublist.trans ?_ hLT
    rw [hL]
    exact (List.sublist_append_right u B).trans (List.sublist_append_left _ v)
  have hvL : v <+ T := by
    refine List.Sublist.trans ?_ hLT
    rw [hL]
    exact List.sublist_append_right _ v
  obtain ⟨u', x₁, hu⟩ : ∃ u' x₁, u = u' ++ [x₁] :=
    ⟨_, _, (List.dropLast_concat_getLast (List.ne_nil_of_mem he₁u)).symm⟩
  obtain ⟨z₁, B', hB₁⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hyB)
  obtain ⟨B'', x₂, hB₂⟩ : ∃ B'' x₂, B = B'' ++ [x₂] :=
    ⟨_, _, (List.dropLast_concat_getLast (List.ne_nil_of_mem hyB)).symm⟩
  obtain ⟨z₂, v', hv⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem he₂v)
  have hx₁u : x₁ ∈ u := by
    rw [hu]
    exact List.mem_append_right u' (List.mem_singleton_self x₁)
  have hz₁B : z₁ ∈ B := by
    rw [hB₁]
    exact List.mem_cons_self
  have hx₂B : x₂ ∈ B := by
    rw [hB₂]
    exact List.mem_append_right B'' (List.mem_singleton_self x₂)
  have hz₂v : z₂ ∈ v := by
    rw [hv]
    exact List.mem_cons_self
  have hx₁t : x₁ ∈ t := mem_of_between_or_eq hnd ht he₁m hym
    (eq_or_pair_sublist_of_concat hu he₁u huL) (Or.inr (hi hx₁u hyB))
  have hz₁t : z₁ ∈ t := mem_of_between_or_eq hnd ht he₁m hym
    (Or.inr (hi he₁u hz₁B)) (eq_or_pair_sublist_of_cons hB₁ hyB hBL)
  have hx₂t : x₂ ∈ t := mem_of_between_or_eq hnd ht hym he₂m
    (eq_or_pair_sublist_of_concat hB₂ hyB hBL) (Or.inr (hii hx₂B he₂v))
  have hz₂t : z₂ ∈ t := mem_of_between_or_eq hnd ht hym he₂m
    (Or.inr (hii hyB hz₂v)) (eq_or_pair_sublist_of_cons hv he₂v hvL)
  refine hbad ⟨⟨x₁, Option.mem_def.mpr (by rw [hu, List.getLast?_concat]), z₁,
      Option.mem_def.mpr (by rw [hB₁, List.head?_cons]), ?_⟩,
    ⟨x₂, Option.mem_def.mpr (by rw [hB₂, List.getLast?_concat]), z₂,
      Option.mem_def.mpr (by rw [hv, List.head?_cons]), ?_⟩⟩
  · refine exists_adjacent_of_runConvex (u := u') (w := B' ++ v) hnd hLT ht hconv ?_ hx₁t hz₁t
    rw [hL, hu, hB₁]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  · refine exists_adjacent_of_runConvex (u := u ++ B'') (w := v') hnd hLT ht hconv ?_ hx₂t hz₂t
    rw [hL, hB₂, hv]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.runConvex_outer

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
