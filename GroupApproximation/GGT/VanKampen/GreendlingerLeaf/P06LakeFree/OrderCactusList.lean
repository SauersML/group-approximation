import Mathlib.Data.List.Rotate
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P06, cactus order: contiguous pieces of a sublist (lane gl-p06-14)

List combinatorics for `P06LakeFree.cellPocketLakeFreeEnclosedOrder_of_cactusOrder`
(`P06LakeFree/OrderCactusStatement.lean`).  Osin, arXiv:math/0411039v3, §9, proof of
Lemma 9.7(b), item 5 (contiguity) of the truth check of `P06LakeFree/EnclosedOrder.lean`.

## The mathematical proof

`RunConvex l t` says: whenever an entry `y` of `t` is off `l`, all of `l` on `t` lies on one side of
`y` (the entries of `t` before `y` are off `l`, or the entries after `y` are off `l`).

1. *Prefix* (`exists_append_of_cons_sublist`).  If `x :: t` has no repeated entry, `r <+ t` and
   `x :: r` is convex in `x :: t`, then `r` is a prefix of `t`.  Induction on `t = y :: t'`.  If
   `r <+ t'` and `r = z :: _`, then `y` is off `x :: r` (no repeats), and both sides of `y` meet
   `x :: r` (`x` before, `z` after): impossible.  Otherwise `r = y :: r'`, `r' <+ t'`, and `y :: r'`
   is convex in `y :: t'`: an entry `w` of `y :: t'` off `y :: r'` is not `x`, so the convexity of
   `x :: y :: r'` applies with `x` in front; the front side meets `x`, so the back side is off.
2. *Infix* (`exists_infix_of_sublist`).  If `t` has no repeated entry, `l <+ t` and `l` is convex in
   `t`, then `t = p ++ l ++ r`.  Induction on `t = x :: t'`: either `l <+ t'` (convexity passes to
   the tail) or `l = x :: r` with `r <+ t'`, and item 1 applies.
3. *Four pieces* (`exists_four_of_sublist`).  If `fS ++ A ++ sS ++ B` has no repeated entry and
   `l <+ fS ++ A ++ sS ++ B` is convex in `A` and in `B`, then `l = s₁ ++ q₁ ++ s₂ ++ q₂` with
   `s₁ <+ fS`, `s₂ <+ sS` and `q₁`, `q₂` infixes of `A`, `B`.  Split the sublist
   (`List.sublist_append_iff`); by no repeats, the entries of `l` on `A` are exactly those of `q₁`,
   so `q₁` is convex in `A` (`RunConvex.mono`) and item 2 applies; likewise for `q₂`.

Truth check: item 1 needs no repeats (`t = [a, b, b, a]`, `l = [a, b, a]` is convex but no
infix); all three are list facts over any type.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus

variable {α : Type*}

/-- **Convexity of a sublist.**  Whenever an entry `y` of `t` is off `l`, the entries of `t` before
`y` are all off `l`, or the entries after `y` are all off `l`. -/
def RunConvex (l t : List α) : Prop :=
  ∀ u y v, t = u ++ y :: v → y ∉ l → (∀ e ∈ u, e ∉ l) ∨ (∀ e ∈ v, e ∉ l)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.RunConvex

/-- Convexity passes to the tail. -/
theorem RunConvex.tail {x : α} {l t : List α} (h : RunConvex l (x :: t)) : RunConvex l t := by
  intro u y v ht hy
  rcases h (x :: u) y v (by rw [ht, List.cons_append]) hy with h' | h'
  · exact Or.inl fun e he => h' e (List.mem_cons_of_mem x he)
  · exact Or.inr h'

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.RunConvex.tail

/-- Convexity passes to a list with the same entries on `t`. -/
theorem RunConvex.mono {l l' t : List α} (h : RunConvex l t) (h₁ : ∀ e ∈ t, e ∈ l → e ∈ l')
    (h₂ : ∀ e ∈ l', e ∈ l) : RunConvex l' t := by
  intro u y v ht hy
  have hyt : y ∈ t := by
    rw [ht]
    exact List.mem_append_right u List.mem_cons_self
  rcases h u y v ht (fun hm => hy (h₁ y hyt hm)) with h' | h'
  · exact Or.inl fun e he hm => h' e he (h₂ e hm)
  · exact Or.inr fun e he hm => h' e he (h₂ e hm)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.RunConvex.mono

/-- **A convex sublist behind a common head is a prefix.** -/
theorem exists_append_of_cons_sublist (t : List α) :
    ∀ (x : α) (r : List α), (x :: t).Nodup → r <+ t → RunConvex (x :: r) (x :: t) →
      ∃ rest, t = r ++ rest := by
  induction t with
  | nil =>
    intro _ r _ hr _
    exact ⟨[], by simp only [List.sublist_nil.1 hr, List.append_nil]⟩
  | cons y t ih =>
    intro x r hn hr hc
    rcases List.sublist_cons_iff.1 hr with hr' | ⟨r', rfl, hr'⟩
    · cases r with
      | nil => exact ⟨y :: t, rfl⟩
      | cons z r'' =>
        exfalso
        have hy : y ∉ x :: z :: r'' := by
          intro hm
          rcases List.mem_cons.1 hm with hyx | hyr
          · exact (List.nodup_cons.1 hn).1 (by rw [← hyx]; exact List.mem_cons_self)
          · exact (List.nodup_cons.1 (List.nodup_cons.1 hn).2).1 (hr'.subset hyr)
        rcases hc [x] y t rfl hy with h' | h'
        · exact h' x List.mem_cons_self List.mem_cons_self
        · exact h' z (hr'.subset List.mem_cons_self) (List.mem_cons_of_mem x List.mem_cons_self)
    · have hc' : RunConvex (y :: r') (y :: t) := by
        intro u w v ht hw
        have hwt : w ∈ y :: t := by
          rw [ht]
          exact List.mem_append_right u List.mem_cons_self
        have hwx : w ∉ x :: y :: r' := by
          intro hm
          rcases List.mem_cons.1 hm with hwx | hwr
          · exact (List.nodup_cons.1 hn).1 (by rw [← hwx]; exact hwt)
          · exact hw hwr
        rcases hc (x :: u) w v (by rw [ht, List.cons_append]) hwx with h' | h'
        · exact (h' x List.mem_cons_self List.mem_cons_self).elim
        · exact Or.inr fun e he hm => h' e he (List.mem_cons_of_mem x hm)
      obtain ⟨rest, hrest⟩ := ih y r' (List.nodup_cons.1 hn).2 hr' hc'
      exact ⟨rest, by rw [hrest, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.exists_append_of_cons_sublist

/-- **A convex sublist of a list without repeats is an infix.** -/
theorem exists_infix_of_sublist (t : List α) :
    ∀ l : List α, t.Nodup → l <+ t → RunConvex l t → ∃ p r, t = p ++ l ++ r := by
  induction t with
  | nil =>
    intro l _ hl _
    exact ⟨[], [], by simp only [List.sublist_nil.1 hl, List.append_nil]⟩
  | cons x t ih =>
    intro l hn hl hc
    rcases List.sublist_cons_iff.1 hl with hl' | ⟨r, rfl, hr⟩
    · obtain ⟨p, r, hpr⟩ := ih l (List.nodup_cons.1 hn).2 hl' hc.tail
      exact ⟨x :: p, r, by simp only [hpr, List.cons_append]⟩
    · obtain ⟨rest, hrest⟩ := exists_append_of_cons_sublist t x r hn hr hc
      exact ⟨[], rest, by simp only [hrest, List.nil_append, List.cons_append]⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.exists_infix_of_sublist

/-- **A convex sublist of four blocks reads four pieces.**  If `fS ++ A ++ sS ++ B` has no repeats
and `l` is a sublist of it, convex in `A` and in `B`, then `l = s₁ ++ q₁ ++ s₂ ++ q₂` with
`s₁ <+ fS`, `s₂ <+ sS`, and `q₁`, `q₂` infixes of `A`, `B`. -/
theorem exists_four_of_sublist {fS A sS B l : List α} (hc : (fS ++ A ++ sS ++ B).Nodup)
    (hl : l <+ fS ++ A ++ sS ++ B) (hA : RunConvex l A) (hB : RunConvex l B) :
    ∃ p₁ q₁ r₁ p₂ q₂ r₂ s₁ s₂ : List α,
      A = p₁ ++ q₁ ++ r₁ ∧ B = p₂ ++ q₂ ++ r₂ ∧ s₁ <+ fS ∧ s₂ <+ sS ∧
        l = s₁ ++ q₁ ++ s₂ ++ q₂ := by
  obtain ⟨l₃, q₂, rfl, h₃, hq₂⟩ := List.sublist_append_iff.1 hl
  obtain ⟨l₂, s₂, rfl, h₂, hs₂⟩ := List.sublist_append_iff.1 h₃
  obtain ⟨s₁, q₁, rfl, hs₁, hq₁⟩ := List.sublist_append_iff.1 h₂
  have hc₁ := List.nodup_append.1 hc
  have hc₂ := List.nodup_append.1 hc₁.1
  have hc₃ := List.nodup_append.1 hc₂.1
  have hA' : RunConvex q₁ A := by
    refine hA.mono (fun e he hm => ?_) (fun e he => ?_)
    · simp only [List.mem_append] at hm
      rcases hm with ((h | h) | h) | h
      · exact (hc₃.2.2 e (hs₁.subset h) e he rfl).elim
      · exact h
      · exact (hc₂.2.2 e (List.mem_append_right fS he) e (hs₂.subset h) rfl).elim
      · exact (hc₁.2.2 e (List.mem_append_left sS (List.mem_append_right fS he)) e
          (hq₂.subset h) rfl).elim
    · simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inr he))
  have hB' : RunConvex q₂ B := by
    refine hB.mono (fun e he hm => ?_) (fun e he => ?_)
    · simp only [List.mem_append] at hm
      rcases hm with ((h | h) | h) | h
      · exact (hc₁.2.2 e (List.mem_append_left sS (List.mem_append_left A (hs₁.subset h))) e
          he rfl).elim
      · exact (hc₁.2.2 e (List.mem_append_left sS (List.mem_append_right fS (hq₁.subset h))) e
          he rfl).elim
      · exact (hc₁.2.2 e (List.mem_append_right (fS ++ A) (hs₂.subset h)) e he rfl).elim
      · exact h
    · simp only [List.mem_append]
      exact Or.inr he
  obtain ⟨p₁, r₁, hA''⟩ := exists_infix_of_sublist A q₁ hc₃.2.1 hq₁ hA'
  obtain ⟨p₂, r₂, hB''⟩ := exists_infix_of_sublist B q₂ hc₁.2.1 hq₂ hB'
  exact ⟨p₁, q₁, r₁, p₂, q₂, r₂, s₁, s₂, hA'', hB'', hs₁, hs₂, rfl⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus.exists_four_of_sublist

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P06LakeFree.OrderCactus
