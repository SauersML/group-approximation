import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece10Live.GFaceWindCore
import Mathlib.Data.List.Chain
import Mathlib.Logic.Relation
import GroupApproximation.Meta.AxiomGuard

/-!
# Winding choice of `F'`: gap-free arcs and walk regions

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-57.

Two facts used by `Piece10Live/GFaceWindClause` to discharge clauses 4, 8 and 9 of the
winding choice of `F'` (`Piece10Live/GFaceWind`) from properties of the walk alone.

* `gfaceWindClause_block`: on a gap-free list `t` (no `a`, then a nonempty gap, then `b` with
  `R a b`), a filter of `t` that is an `R`-chain is one contiguous block of `t`.
* `gfaceWindClause_const`: a face function cobounded by a sub-list `c` of `C` is constant along
  steps across edges off `C`, hence on the walk region of a face.

## Truth check

`gfaceWindClause_block` is list combinatorics; `gfaceWindClause_const` is the coboundary
identity with both indicators zero.  See `Piece10Live/GFaceWindClause` for the assembled check.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

universe v

open scoped Classical

section Block

variable {α : Type*}

/-- **A gap-free list**: no entry `a` is followed, after a nonempty gap `z`, by an entry `b`
with `R a b`. -/
def gfaceWindClause_Gap (R : α → α → Prop) (t : List α) : Prop :=
  ∀ (pre z post : List α) (a b : α), t = pre ++ a :: (z ++ b :: post) → z ≠ [] → ¬ R a b

theorem gfaceWindClause_gap_tail {R : α → α → Prop} {x : α} {t : List α}
    (h : gfaceWindClause_Gap R (x :: t)) : gfaceWindClause_Gap R t := by
  intro pre z post a b ht hz
  exact h (x :: pre) z post a b (by rw [ht, List.cons_append]) hz

/-- **The first entry passing a filter.** -/
theorem gfaceWindClause_first {P : α → Bool} :
    ∀ {t : List α}, t.filter P ≠ [] →
      ∃ (z : List α) (b : α) (post : List α), t = z ++ b :: post ∧
        (∀ a ∈ z, P a = false) ∧ P b = true
  | [], h => absurd rfl h
  | x :: t, h => by
    cases hx : P x
    · have hx' : ¬ P x = true := by simp [hx]
      rw [List.filter_cons_of_neg hx'] at h
      obtain ⟨z, b, post, ht, hz, hb⟩ := gfaceWindClause_first h
      refine ⟨x :: z, b, post, by rw [ht, List.cons_append], fun a ha => ?_, hb⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hx
      · exact hz a ha
    · exact ⟨[], x, t, rfl, fun a ha => absurd ha List.not_mem_nil, hx⟩

/-- **A chain filter starting at the head is a prefix block.** -/
theorem gfaceWindClause_head {R : α → α → Prop} {P : α → Bool} :
    ∀ {t : List α} {x : α}, P x = true → gfaceWindClause_Gap R (x :: t) →
      ((x :: t).filter P).IsChain R →
        ∃ mid post : List α, x :: t = mid ++ post ∧ (x :: t).filter P = mid
  | [], x, hx, _, _ => ⟨[x], [], rfl, by rw [List.filter_cons_of_pos hx, List.filter_nil]⟩
  | y :: t, x, hx, hg, hc => by
    cases hy : P y
    · have hy' : ¬ P y = true := by simp [hy]
      have hnil : t.filter P = [] := by
        by_contra hne
        obtain ⟨z, b, post, ht, hz, hb⟩ := gfaceWindClause_first hne
        have hz0 : z.filter P = [] := List.filter_eq_nil_iff.mpr fun a ha => by simp [hz a ha]
        have hfz : (z ++ b :: post).filter P = b :: post.filter P := by
          rw [List.filter_append, hz0, List.filter_cons_of_pos hb, List.nil_append]
        rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg hy', ht, hfz,
          List.isChain_cons_cons] at hc
        exact hg [] (y :: z) post x b (by rw [ht, List.nil_append, List.cons_append])
          (List.cons_ne_nil y z) hc.1
      refine ⟨[x], y :: t, rfl, ?_⟩
      rw [List.filter_cons_of_pos hx, List.filter_cons_of_neg hy', hnil]
    · rw [List.filter_cons_of_pos hx, List.filter_cons_of_pos hy, List.isChain_cons_cons] at hc
      have hc2 : ((y :: t).filter P).IsChain R := by
        rw [List.filter_cons_of_pos hy]
        exact hc.2
      obtain ⟨mid, post, h1, h2⟩ := gfaceWindClause_head hy (gfaceWindClause_gap_tail hg) hc2
      refine ⟨x :: mid, post, by rw [h1, List.cons_append], ?_⟩
      rw [List.filter_cons_of_pos hx, h2]

/-- **Gap-free lists have block chain filters**: on a gap-free list, a filter that is an
`R`-chain is one contiguous block. -/
theorem gfaceWindClause_block {R : α → α → Prop} {P : α → Bool} :
    ∀ {t : List α}, gfaceWindClause_Gap R t → (t.filter P).IsChain R →
      ∃ pre mid post : List α, t = pre ++ mid ++ post ∧ t.filter P = mid
  | [], _, _ => ⟨[], [], [], rfl, rfl⟩
  | x :: t, hg, hc => by
    cases hx : P x
    · have hx' : ¬ P x = true := by simp [hx]
      rw [List.filter_cons_of_neg hx'] at hc
      obtain ⟨pre, mid, post, h1, h2⟩ := gfaceWindClause_block (gfaceWindClause_gap_tail hg) hc
      refine ⟨x :: pre, mid, post, by rw [h1, List.cons_append, List.cons_append], ?_⟩
      rw [List.filter_cons_of_neg hx', h2]
    · obtain ⟨mid, post, h1, h2⟩ := gfaceWindClause_head hx hg hc
      exact ⟨[], mid, post, by rw [h1, List.nil_append], h2⟩

end Block

/-- **A step across an edge off the walk `C`**, from the face of `x` to the face of `alpha x`. -/
def gfaceWindClause_Adj (M : CombMap.{v}) (C : List M.Dart) (f f' : M.Face) : Prop :=
  ∃ x, x ∉ C ∧ M.alpha x ∉ C ∧ M.faceOf x = f ∧ M.faceOf (M.alpha x) = f'

/-- **Constancy on walk regions**: a face function cobounded by a sub-list `c` of `C` takes the
same value at faces joined by steps across edges off `C`. -/
theorem gfaceWindClause_const {M : CombMap.{v}} {C c : List M.Dart} {g : M.Face → ℤ}
    (hsub : ∀ x ∈ c, x ∈ C)
    (hcob : ∀ d, g (M.faceOf d) - g (M.faceOf (M.alpha d)) =
      gfaceWind_lind c d - gfaceWind_lind c (M.alpha d))
    {f f' : M.Face} (h : Relation.ReflTransGen (gfaceWindClause_Adj M C) f f') :
    g f = g f' := by
  induction h with
  | refl => rfl
  | tail _ hst ih =>
    obtain ⟨x, hx1, hx2, rfl, rfl⟩ := hst
    have hx1' : x ∉ c := fun hx => hx1 (hsub x hx)
    have hx2' : M.alpha x ∉ c := fun hx => hx2 (hsub _ hx)
    have h1 := hcob x
    linarith [gfaceWind_lind_neg hx1', gfaceWind_lind_neg hx2']

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_Gap
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_gap_tail
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_first
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_head
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_block
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_Adj
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.GFaceWind.gfaceWindClause_const
