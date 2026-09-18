import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactusList
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus petal: order facts in a list without repeats (lane gl-p06-18)

List combinatorics for `P06LakeFree.PetalTurn.cellPocketLakeFreePetalTurn`
(`P06LakeFree/PetalTurnClose.lean`).  Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).

## The mathematical proof

Write `x ≺ y` for `[x, y] <+ T`.

1. *Antisymmetry* (`pair_sublist_antisymm`).  If `T` has no repeated entry, `x ≺ y` and `y ≺ x`
   are incompatible.  Induction on `T = a :: T'`: if both pairs sit in `T'` use induction; if one
   of them starts at `a`, the other entry of that pair is `a` too or lies in `T'`, and in both
   cases `a ∈ T'`.
2. *Betweenness* (`mem_of_between`).  If `t` is an infix of `T = P ++ t ++ R`, `a, c ∈ t` and
   `a ≺ b ≺ c`, then `b ∈ t`: `b ∈ P` gives `b ≺ a`, `b ∈ R` gives `c ≺ b`.
3. *Adjacency* (`exists_adjacent_of_runConvex`).  If `L <+ T`, `t <:+: T`, `L` is convex in `t`,
   `L = u ++ x :: z :: w` and `x, z ∈ t`, then `x :: z` is an infix of `t`.  Split
   `t = p ++ x :: r ++ z :: s` (`z ∉ p` by antisymmetry).  If `r = w₀ :: _`, then `x ≺ w₀ ≺ z`.
   An entry `w₀` off `L` has `x` in front and `z` behind, against convexity; an entry `w₀` of `L`
   lies in `u` (`w₀ ≺ x`), equals `x` or `z` (a repeat), or lies in `w` (`z ≺ w₀`).

Truth check: without "no repeats" antisymmetry fails (`T = [a, b, a]`); all items are list facts
over any type.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn

variable {α : Type*}

/-- **Antisymmetry of the order of a list without repeats.** -/
theorem pair_sublist_antisymm {x y : α} {T : List α} (hnd : T.Nodup) (h₁ : [x, y] <+ T)
    (h₂ : [y, x] <+ T) : False := by
  induction T with
  | nil => exact List.cons_ne_nil _ _ (List.sublist_nil.mp h₁)
  | cons a T ih =>
    obtain ⟨ha, hT⟩ := List.nodup_cons.mp hnd
    rcases List.sublist_cons_iff.mp h₁ with h₁ | ⟨r₁, hr₁, hs₁⟩ <;>
      rcases List.sublist_cons_iff.mp h₂ with h₂ | ⟨_, hr₂, -⟩
    · exact ih hT h₁ h₂
    · exact ha (by
        rw [← (List.cons.inj hr₂).1]
        exact h₁.subset (List.mem_cons_of_mem x List.mem_cons_self))
    · exact ha (by
        rw [← (List.cons.inj hr₁).1]
        exact h₂.subset (List.mem_cons_of_mem y List.mem_cons_self))
    · have hy : y ∈ r₁ := by
        rw [← (List.cons.inj hr₁).2]
        exact List.mem_singleton_self y
      exact ha (by
        rw [← (List.cons.inj hr₂).1]
        exact hs₁.subset hy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.pair_sublist_antisymm

/-- An entry of the first piece comes before an entry of the second piece. -/
theorem pair_sublist_append {x y : α} {l₁ l₂ : List α} (hx : x ∈ l₁) (hy : y ∈ l₂) :
    [x, y] <+ l₁ ++ l₂ :=
  (List.singleton_sublist.mpr hx).append (List.singleton_sublist.mpr hy)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.pair_sublist_append

/-- An entry comes before the entries behind it. -/
theorem pair_sublist_of_eq {t p q : List α} {x y : α} (h : t = p ++ x :: q) (hy : y ∈ q) :
    [x, y] <+ t := by
  rw [h]
  exact (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hy)).trans
    (List.sublist_append_right p _)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.pair_sublist_of_eq

/-- **Betweenness.**  An entry between two entries of an infix lies on the infix. -/
theorem mem_of_between {T t : List α} {a b c : α} (hnd : T.Nodup) (ht : t <:+: T) (ha : a ∈ t)
    (hc : c ∈ t) (hab : [a, b] <+ T) (hbc : [b, c] <+ T) : b ∈ t := by
  obtain ⟨P, R, hT⟩ := ht
  subst hT
  have hb : b ∈ P ++ t ++ R := hab.subset (List.mem_cons_of_mem a List.mem_cons_self)
  rcases List.mem_append.mp hb with hb | hb
  · rcases List.mem_append.mp hb with hb | hb
    · refine (pair_sublist_antisymm hnd hab ?_).elim
      rw [List.append_assoc]
      exact pair_sublist_append hb (List.mem_append_left R ha)
    · exact hb
  · exact (pair_sublist_antisymm hnd hbc
      (pair_sublist_append (List.mem_append_right P hc) hb)).elim

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.mem_of_between

/-- **Adjacency.**  Two consecutive entries of a convex sublist lying on an infix are consecutive
on the infix. -/
theorem exists_adjacent_of_runConvex {T L t u w : List α} {x z : α} (hnd : T.Nodup)
    (hLT : L <+ T) (ht : t <:+: T) (hconv : OrderCactus.RunConvex L t)
    (hL : L = u ++ x :: z :: w) (hx : x ∈ t) (hz : z ∈ t) :
    ∃ p q, t = p ++ x :: z :: q := by
  have hxL : x ∈ L := by
    rw [hL]
    exact List.mem_append_right u List.mem_cons_self
  have hzL : z ∈ L := by
    rw [hL]
    exact List.mem_append_right u (List.mem_cons_of_mem x List.mem_cons_self)
  have hxz : [x, z] <+ T := (pair_sublist_of_eq hL List.mem_cons_self).trans hLT
  obtain ⟨p, q₀, rfl⟩ := List.append_of_mem hx
  have htT : p ++ x :: q₀ <+ T := ht.sublist
  have hzq : z ∈ q₀ := by
    rcases List.mem_append.mp hz with hz' | hz'
    · exact (pair_sublist_antisymm hnd hxz
        ((pair_sublist_append hz' List.mem_cons_self).trans htT)).elim
    · rcases List.mem_cons.mp hz' with rfl | hz''
      · exact (pair_sublist_antisymm hnd hxz hxz).elim
      · exact hz''
  obtain ⟨r, s, rfl⟩ := List.append_of_mem hzq
  cases r with
  | nil => exact ⟨p, s, rfl⟩
  | cons w₀ r =>
    exfalso
    have hsub : w₀ :: (r ++ z :: s) <+ T :=
      ((List.sublist_cons_self x _).trans (List.sublist_append_right p _)).trans htT
    have hxw : [x, w₀] <+ T := by
      refine List.Sublist.trans ?_ htT
      exact pair_sublist_of_eq rfl (List.mem_append_left (z :: s) List.mem_cons_self)
    have hwz : [w₀, z] <+ T :=
      (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr
        (List.mem_append_right r List.mem_cons_self))).trans hsub
    by_cases hw₀ : w₀ ∈ L
    · rw [hL] at hw₀
      rcases List.mem_append.mp hw₀ with hu | hw₀
      · refine pair_sublist_antisymm hnd hxw (List.Sublist.trans ?_ hLT)
        rw [hL]
        exact pair_sublist_append hu List.mem_cons_self
      · rcases List.mem_cons.mp hw₀ with rfl | hw₀
        · exact pair_sublist_antisymm hnd hxw hxw
        · rcases List.mem_cons.mp hw₀ with rfl | hw
          · exact pair_sublist_antisymm hnd hwz hwz
          · refine pair_sublist_antisymm hnd hwz (List.Sublist.trans ?_ hLT)
            rw [hL]
            exact (List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hw)).trans
              ((List.sublist_cons_self x _).trans (List.sublist_append_right u _))
    · have heq : p ++ x :: (w₀ :: r ++ z :: s) = (p ++ [x]) ++ w₀ :: (r ++ z :: s) := by
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      rcases hconv (p ++ [x]) w₀ (r ++ z :: s) heq hw₀ with h | h
      · exact h x (List.mem_append_right p List.mem_cons_self) hxL
      · exact h z (List.mem_append_right r List.mem_cons_self) hzL

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn.exists_adjacent_of_runConvex

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.PetalTurn
