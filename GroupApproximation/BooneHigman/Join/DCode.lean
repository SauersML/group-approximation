import GroupApproximation.BooneHigman.Join.DPent
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Range

/-!
# Complete prefix codes over `Fin (n + 2)`, in order (lane bh-pal-met-join)

`IsCode n L`: `L` is obtained from `[[]]` by repeatedly replacing a word `d` by its children
`d 0, …, d t`, in place.  Then:
* the words of `L` are pairwise incomparable (`IsCode.pairwise`);
* consecutive words are adjacent, `DAdj (w i t^a) (w (i+1) 0^b)` (`IsCode.chain`);
* every word of large length has a prefix in `L` (`IsCode.cover`).
`exF L d` is the set of words of `L` with `d` replaced by its children.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope

variable {n : ℕ}

/-- The children `d 0, …, d t` of a word. -/
def children (n : ℕ) (d : List (Fin (n + 2))) : List (List (Fin (n + 2))) :=
  (List.range (n + 2)).map fun i => d ++ [fc n i]

#audit_axioms GroupApproximation.BooneHigman.Join.children

theorem mem_children {d c : List (Fin (n + 2))} :
    c ∈ children n d ↔ ∃ a : Fin (n + 2), c = d ++ [a] := by
  unfold children
  rw [List.mem_map]
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨fc n i, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, List.mem_range.mpr a.isLt, by rw [fc_val]⟩

#audit_axioms GroupApproximation.BooneHigman.Join.mem_children

theorem child_mem (d : List (Fin (n + 2))) (a : Fin (n + 2)) : d ++ [a] ∈ children n d :=
  mem_children.mpr ⟨a, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.child_mem

/-- Incomparable words. -/
def Inc {X : Type*} (u v : List X) : Prop := ¬ u <+: v ∧ ¬ v <+: u

#audit_axioms GroupApproximation.BooneHigman.Join.Inc

theorem Inc.symm {X : Type*} {u v : List X} (h : Inc u v) : Inc v u := ⟨h.2, h.1⟩

#audit_axioms GroupApproximation.BooneHigman.Join.Inc.symm

theorem Inc.ext {X : Type*} {u v : List X} (h : Inc u v) (a b : List X) : Inc (u ++ a) (v ++ b) :=
  ⟨dinc_append h.1 h.2 a b, dinc_append h.2 h.1 b a⟩

#audit_axioms GroupApproximation.BooneHigman.Join.Inc.ext

theorem Inc.extl {X : Type*} {u v : List X} (h : Inc u v) (a : List X) : Inc (u ++ a) v := by
  have h' := h.ext a []
  rwa [List.append_nil] at h'

#audit_axioms GroupApproximation.BooneHigman.Join.Inc.extl

theorem children_pairwise (d : List (Fin (n + 2))) : (children n d).Pairwise Inc := by
  unfold children
  rw [List.pairwise_map]
  refine List.nodup_range.imp_of_mem fun {i j} hi hj hij => ?_
  have hne := fc_ne (n := n) (List.mem_range.mp hi) (List.mem_range.mp hj) hij
  exact ⟨dinc_child d hne, dinc_child d hne.symm⟩

#audit_axioms GroupApproximation.BooneHigman.Join.children_pairwise

/-- Adjacent words: `w i t^a` and `w (i+1) 0^b`. -/
def DAdj (u v : List (Fin (n + 2))) : Prop :=
  ∃ w i a b, i ≤ n ∧ u = w ++ fc n i :: List.replicate a (tl n) ∧
    v = w ++ fc n (i + 1) :: List.replicate b (fc n 0)

#audit_axioms GroupApproximation.BooneHigman.Join.DAdj

theorem dadj_child_left {x d : List (Fin (n + 2))} (h : DAdj x d) : DAdj x (d ++ [fc n 0]) := by
  obtain ⟨w, i, a, b, hi, rfl, rfl⟩ := h
  refine ⟨w, i, a, b + 1, hi, rfl, ?_⟩
  rw [List.replicate_succ']
  simp

#audit_axioms GroupApproximation.BooneHigman.Join.dadj_child_left

theorem dadj_child_right {d y : List (Fin (n + 2))} (h : DAdj d y) : DAdj (d ++ [tl n]) y := by
  obtain ⟨w, i, a, b, hi, rfl, rfl⟩ := h
  refine ⟨w, i, a + 1, b, hi, ?_, rfl⟩
  rw [List.replicate_succ']
  simp

#audit_axioms GroupApproximation.BooneHigman.Join.dadj_child_right

theorem children_chain (d : List (Fin (n + 2))) : (children n d).IsChain DAdj := by
  unfold children
  rw [List.isChain_map, List.isChain_range_succ]
  intro m hm
  exact ⟨d, m, 0, 0, by omega, rfl, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.children_chain

theorem children_head (d : List (Fin (n + 2))) : (children n d).head? = some (d ++ [fc n 0]) := by
  unfold children
  rw [List.range_succ_eq_map]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Join.children_head

theorem children_last (d : List (Fin (n + 2))) : (children n d).getLast? = some (d ++ [tl n]) := by
  unfold children
  rw [List.range_succ, List.map_append, List.getLast?_append]
  rfl

#audit_axioms GroupApproximation.BooneHigman.Join.children_last

/-- Codes: obtained from `[[]]` by in-place expansions. -/
inductive IsCode (n : ℕ) : List (List (Fin (n + 2))) → Prop
  | root : IsCode n [[]]
  | exp (L₁ L₂ : List (List (Fin (n + 2)))) (d : List (Fin (n + 2))) :
      IsCode n (L₁ ++ d :: L₂) → IsCode n (L₁ ++ (children n d ++ L₂))

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode

theorem IsCode.pairwise {L : List (List (Fin (n + 2)))} (h : IsCode n L) : L.Pairwise Inc := by
  induction h with
  | root => exact List.pairwise_singleton _ _
  | exp L₁ L₂ d _ ih =>
    rw [List.pairwise_append, List.pairwise_cons] at ih
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := ih
    rw [List.pairwise_append, List.pairwise_append]
    refine ⟨h1, ⟨children_pairwise d, h3, fun a ha b hb => ?_⟩, fun a ha b hb => ?_⟩
    · obtain ⟨x, rfl⟩ := mem_children.mp ha
      exact (h2 b hb).extl [x]
    · rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨x, rfl⟩ := mem_children.mp hb
        exact ((h4 a ha d List.mem_cons_self).symm.extl [x]).symm
      · exact h4 a ha b (List.mem_cons_of_mem d hb)

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.pairwise

theorem IsCode.chain {L : List (List (Fin (n + 2)))} (h : IsCode n L) : L.IsChain DAdj := by
  induction h with
  | root => exact List.isChain_singleton _
  | exp L₁ L₂ d _ ih =>
    rw [List.isChain_append, List.isChain_cons] at ih
    obtain ⟨h1, ⟨h2, h3⟩, h4⟩ := ih
    rw [List.isChain_append, List.isChain_append]
    refine ⟨h1, ⟨children_chain d, h3, fun x hx y hy => ?_⟩, fun x hx y hy => ?_⟩
    · rw [children_last, Option.mem_some_iff] at hx
      subst hx
      exact dadj_child_right (h2 y hy)
    · rw [List.head?_append, children_head, Option.some_or, Option.mem_some_iff] at hy
      subst hy
      exact dadj_child_left (h4 x hx d rfl)

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.chain

theorem IsCode.cover {L : List (List (Fin (n + 2)))} (h : IsCode n L) :
    ∃ D, (∀ c ∈ L, c.length ≤ D) ∧ ∀ w : List (Fin (n + 2)), D ≤ w.length → ∃ c ∈ L, c <+: w := by
  induction h with
  | root => exact ⟨0, fun c hc => by simp at hc; simp [hc], fun w _ => ⟨[], by simp, List.nil_prefix⟩⟩
  | exp L₁ L₂ d _ ih =>
    obtain ⟨D, hD, hw⟩ := ih
    refine ⟨D + 1, fun c hc => ?_, fun w hwl => ?_⟩
    · rcases List.mem_append.mp hc with hc | hc
      · exact (hD c (List.mem_append_left _ hc)).trans (Nat.le_succ D)
      · rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨x, rfl⟩ := mem_children.mp hc
          have := hD d (List.mem_append_right _ List.mem_cons_self)
          simp only [List.length_append, List.length_singleton]
          omega
        · exact (hD c (List.mem_append_right _ (List.mem_cons_of_mem d hc))).trans (Nat.le_succ D)
    · obtain ⟨c, hc, hcw⟩ := hw w (by omega)
      rcases List.mem_append.mp hc with hc' | hc'
      · exact ⟨c, List.mem_append_left _ hc', hcw⟩
      · rcases List.mem_cons.mp hc' with rfl | hc''
        · obtain ⟨s, rfl⟩ := hcw
          have hdl := hD c (List.mem_append_right _ List.mem_cons_self)
          cases s with
          | nil => simp at hwl; omega
          | cons x s =>
            refine ⟨c ++ [x], List.mem_append_right _ (List.mem_append_left _ (child_mem c x)), ?_⟩
            exact ⟨s, by simp⟩
        · exact ⟨c, List.mem_append_right _ (List.mem_append_right _ hc''), hcw⟩

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.cover

theorem IsCode.nodup {L : List (List (Fin (n + 2)))} (h : IsCode n L) : L.Nodup :=
  h.pairwise.imp fun hab e => by
    subst e
    exact hab.1 (List.prefix_refl _)

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.nodup

theorem pairwise_inc_mem {X : Type*} {L : List (List X)} (hp : L.Pairwise Inc) {u v : List X}
    (hu : u ∈ L) (hv : v ∈ L) (huv : u ≠ v) : Inc u v := by
  induction L with
  | nil => simp at hu
  | cons a L ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hu with rfl | hu' <;> rcases List.mem_cons.mp hv with rfl | hv'
    · exact absurd rfl huv
    · exact hp.1 v hv'
    · exact (hp.1 u hu').symm
    · exact ih hp.2 hu' hv'

#audit_axioms GroupApproximation.BooneHigman.Join.pairwise_inc_mem

theorem IsCode.inc {L : List (List (Fin (n + 2)))} (h : IsCode n L) {u v : List (Fin (n + 2))}
    (hu : u ∈ L) (hv : v ∈ L) (huv : u ≠ v) : Inc u v :=
  pairwise_inc_mem h.pairwise hu hv huv

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.inc

theorem IsCode.isAC {L : List (List (Fin (n + 2)))} (h : IsCode n L) : IsAC L.toFinset := by
  intro u hu v hv huv
  rw [List.mem_toFinset] at hu hv
  exact (h.inc hu hv huv).1

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.isAC

/-- The words of `L` with `d` replaced by its children. -/
def exF (L : List (List (Fin (n + 2)))) (d : List (Fin (n + 2))) : Finset (List (Fin (n + 2))) :=
  (L.toFinset.erase d) ∪ (children n d).toFinset

#audit_axioms GroupApproximation.BooneHigman.Join.exF

theorem mem_exF {L : List (List (Fin (n + 2)))} {d c : List (Fin (n + 2))} :
    c ∈ exF L d ↔ (c ∈ L ∧ c ≠ d) ∨ ∃ a : Fin (n + 2), c = d ++ [a] := by
  unfold exF
  rw [Finset.mem_union, Finset.mem_erase, List.mem_toFinset, List.mem_toFinset, mem_children]
  tauto

#audit_axioms GroupApproximation.BooneHigman.Join.mem_exF

/-- Expanding a code at one of its words gives a code, with the words `exF L d`. -/
theorem IsCode.expand {L : List (List (Fin (n + 2)))} (h : IsCode n L) {d : List (Fin (n + 2))}
    (hd : d ∈ L) : ∃ L', IsCode n L' ∧ ∀ c, c ∈ L' ↔ c ∈ exF L d := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem hd
  refine ⟨s ++ (children n d ++ t), IsCode.exp s t d h, fun c => ?_⟩
  have hp := h.pairwise
  rw [List.pairwise_append, List.pairwise_cons] at hp
  have hs : d ∉ s := fun hm => (hp.2.2 d hm d (List.mem_cons_self)).1 (List.prefix_refl d)
  have ht : d ∉ t := fun hm => (hp.2.1.1 d hm).1 (List.prefix_refl d)
  rw [mem_exF, ← mem_children]
  simp only [List.mem_append, List.mem_cons]
  constructor
  · rintro (h1 | h1 | h1)
    · exact Or.inl ⟨Or.inl h1, fun e => hs (e ▸ h1)⟩
    · exact Or.inr h1
    · exact Or.inl ⟨Or.inr (Or.inr h1), fun e => ht (e ▸ h1)⟩
  · rintro (⟨h1 | h1 | h1, hne⟩ | h1)
    · exact Or.inl h1
    · exact absurd h1 hne
    · exact Or.inr (Or.inr h1)
    · exact Or.inr (Or.inl h1)

#audit_axioms GroupApproximation.BooneHigman.Join.IsCode.expand

theorem exF_isAC {L : List (List (Fin (n + 2)))} (h : IsCode n L) {d : List (Fin (n + 2))}
    (hd : d ∈ L) : IsAC (exF L d) := by
  obtain ⟨L', hL', hm⟩ := h.expand hd
  intro u hu v hv huv
  exact hL'.isAC u (List.mem_toFinset.mpr ((hm u).mpr hu)) v
    (List.mem_toFinset.mpr ((hm v).mpr hv)) huv

#audit_axioms GroupApproximation.BooneHigman.Join.exF_isAC

end GroupApproximation.BooneHigman.Join
