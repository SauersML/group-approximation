import Mathlib.Data.List.Nodup
import GroupApproximation.Meta.AxiomGuard

/-!
# Extremal minimal: a duplicate-free list segment between two of its members

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-16.

The list lemma behind the arc clauses of `ExtremalClassStretches`: if a duplicate-free list
`F ++ S ++ R` is written as `A ++ d :: (B ++ e :: C)` with `d` and `e` in the middle block `S`,
then every member of the gap `B` lies in `S`.

## Proof route

`mem_segment_of_nodup_aux` (the case `F = []`): split `S ++ R = P ++ d :: (B ++ e :: C)` with
`List.append_eq_append_iff`.  If `d` falls into `R`, `nodup_append` contradicts `d ∈ S`.
Otherwise `S = P ++ bs` and `(d :: B) ++ (e :: C) = bs ++ R`; split again.  If `e` falls into
`R`, contradiction as before; otherwise `bs = (d :: B) ++ as`, so `B ⊆ bs ⊆ S`.

`mem_segment_of_nodup`: split `F ++ (S ++ R) = A ++ d :: (B ++ e :: C)`.  Either `A = F ++ as`
and the auxiliary lemma applies, or `F = A ++ bs` with `bs` a prefix of `d :: ...`: for
`bs = []` the auxiliary lemma applies with `P = []`, and for `bs = b :: _` the dart `d = b` lies
in `F` and in `S`, contradicting `nodup_append`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.7(b));
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

section Lists

variable {α : Type _}

/-- **The gap between two members of a leading block** lies in that block, for a duplicate-free
list. -/
theorem mem_segment_of_nodup_aux {S R P B C : List α} {d e : α} (hnd : (S ++ R).Nodup)
    (h : S ++ R = P ++ d :: (B ++ e :: C)) (hd : d ∈ S) (he : e ∈ S) : ∀ x ∈ B, x ∈ S := by
  intro x hx
  have hdis := (List.nodup_append.mp hnd).2.2
  rcases List.append_eq_append_iff.mp h with ⟨l₁, _, hR⟩ | ⟨bs, hS, hrest⟩
  · have hdR : d ∈ R := by
      rw [hR]
      simp
    exact hdis d hd d hdR rfl
  · have h2 : (d :: B) ++ (e :: C) = bs ++ R := by
      rw [List.cons_append]
      exact hrest
    rcases List.append_eq_append_iff.mp h2 with ⟨l₂, hbs, _⟩ | ⟨bs', _, hR⟩
    · rw [hS, hbs]
      simp [hx]
    · have heR : e ∈ R := by
        rw [hR]
        simp
      exact hdis e he e heR rfl

/-- **The gap between two members of a middle block** lies in that block, for a duplicate-free
list. -/
theorem mem_segment_of_nodup {F S R A B C : List α} {d e : α} (hnd : (F ++ S ++ R).Nodup)
    (h : F ++ S ++ R = A ++ d :: (B ++ e :: C)) (hd : d ∈ S) (he : e ∈ S) : ∀ x ∈ B, x ∈ S := by
  rw [List.append_assoc] at hnd h
  have hSR : (S ++ R).Nodup := (List.nodup_append.mp hnd).2.1
  have hdis := (List.nodup_append.mp hnd).2.2
  rcases List.append_eq_append_iff.mp h with ⟨l₁, _, hrest⟩ | ⟨bs, hF, hrest⟩
  · exact mem_segment_of_nodup_aux hSR hrest hd he
  · rcases bs with _ | ⟨b, bs⟩
    · have h3 : S ++ R = [] ++ d :: (B ++ e :: C) := by
        rw [List.nil_append]
        rw [List.nil_append] at hrest
        exact hrest.symm
      exact mem_segment_of_nodup_aux hSR h3 hd he
    · have hdb : d = b := by
        rw [List.cons_append] at hrest
        exact (List.cons.inj hrest).1
      have hdF : d ∈ F := by
        rw [hF, hdb]
        simp
      have hdSR : d ∈ S ++ R := by simp [hd]
      exact hdis d hdF d hdSR rfl

end Lists

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.mem_segment_of_nodup_aux
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10ExtremalRegion.mem_segment_of_nodup
