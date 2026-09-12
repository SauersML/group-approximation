import GroupApproximation.Matching.PartialBijectionSandwich
import GroupApproximation.Matching.PartialEquivarianceComposition

/-!
# Equivariance defects of transported arrows

Kun and Thom (arXiv:2608.06222, proof of Lemma 4.3) transport an allowed arrow
`b : Q_{π i} ⇢ Q_{π j}` back through the matching bridges of a compressor and
bound the equivariance defect of the result by the defects of `b`, of the two
bridges, and of the label discrepancies.  This file proves the finite counting
behind that bound.

* `card_equivarianceDefect_sandwich_le` and
  `card_symm_equivarianceDefect_sandwich_le`: the forward and backward defects of
  `sandwich u v f` are at most the defects of the bridges plus the defect of `f`.
* `card_equivarianceDefect_congr_le`: replacing the label families on the source
  and the target costs at most the number of labelled points where they differ.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {X X' Y Y' Z : FiniteModel}

/-- Values of a partial bijection at equal points agree, whatever the membership
proofs. -/
theorem apply_eq_of_eq (b : FinitePartialBijection Y Z) {y y' : Y} (h : y = y')
    (hy : y ∈ b.source) (hy' : y' ∈ b.source) : b.apply y hy = b.apply y' hy' := by
  subst h
  rfl

/-! ### Transport through bridges -/

/-- The forward defect of a transported arrow is at most the forward defects of
the reversed source bridge, the arrow, and the target bridge. -/
theorem card_equivarianceDefect_sandwich_le {L : Type*} [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actX' : L → Equiv.Perm X')
    (actY : L → Equiv.Perm Y) (actY' : L → Equiv.Perm Y')
    (u : FinitePartialBijection X X') (v : FinitePartialBijection Y Y')
    (f : FinitePartialBijection X Y) :
    ((sandwich u v f).equivarianceDefect actX' actY').card ≤
      (u.symm.equivarianceDefect actX' actX).card +
        (f.equivarianceDefect actX actY).card +
          (v.equivarianceDefect actY actY').card := by
  have h₁ := card_equivarianceDefect_trans_le actX' actY actY' (u.symm.trans f) v
  have h₂ := card_equivarianceDefect_trans_le actX' actX actY u.symm f
  unfold sandwich
  omega

/-- The backward defect of a transported arrow is at most the backward defects of
the reversed target bridge, the arrow, and the source bridge. -/
theorem card_symm_equivarianceDefect_sandwich_le {L : Type*} [Fintype L] [DecidableEq L]
    (actX : L → Equiv.Perm X) (actX' : L → Equiv.Perm X')
    (actY : L → Equiv.Perm Y) (actY' : L → Equiv.Perm Y')
    (u : FinitePartialBijection X X') (v : FinitePartialBijection Y Y')
    (f : FinitePartialBijection X Y) :
    ((sandwich u v f).symm.equivarianceDefect actY' actX').card ≤
      (v.symm.equivarianceDefect actY' actY).card +
        (f.symm.equivarianceDefect actY actX).card +
          (u.equivarianceDefect actX actX').card := by
  rw [sandwich_symm]
  exact card_equivarianceDefect_sandwich_le actY actY' actX actX' v u f.symm

/-! ### Changing the label families -/

/-- The labelled points where two label families differ. -/
def labelDisagreement {L : Type*} [Fintype L] (act act' : L → Equiv.Perm Y) :
    Finset (L × Y) :=
  Finset.univ.filter fun p ↦ act p.1 p.2 ≠ act' p.1 p.2

@[simp] theorem mem_labelDisagreement {L : Type*} [Fintype L]
    (act act' : L → Equiv.Perm Y) (p : L × Y) :
    p ∈ labelDisagreement act act' ↔ act p.1 p.2 ≠ act' p.1 p.2 := by
  simp [labelDisagreement]

/-- Labelled target points pulled back through a partial bijection. -/
noncomputable def labelPullback {L : Type*} [Fintype L] (b : FinitePartialBijection Y Z)
    (E : Finset (L × Z)) : Finset (L × Y) := by
  classical
  exact Finset.univ.filter fun p ↦ ∃ hy : p.2 ∈ b.source, (p.1, b.apply p.2 hy) ∈ E

@[simp] theorem mem_labelPullback {L : Type*} [Fintype L] (b : FinitePartialBijection Y Z)
    (E : Finset (L × Z)) (p : L × Y) :
    p ∈ b.labelPullback E ↔ ∃ hy : p.2 ∈ b.source, (p.1, b.apply p.2 hy) ∈ E := by
  classical
  simp [labelPullback]

/-- Pulling labelled points back through a partial bijection does not increase
their number. -/
theorem card_labelPullback_le {L : Type*} [Fintype L] (b : FinitePartialBijection Y Z)
    (E : Finset (L × Z)) : (b.labelPullback E).card ≤ E.card := by
  classical
  let F : {p // p ∈ b.labelPullback E} → {q // q ∈ E} := fun p ↦ by
    let hp := (mem_labelPullback b E p.1).mp p.2
    exact ⟨(p.1.1, b.apply p.1.2 hp.choose), hp.choose_spec⟩
  have hF : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun r ↦ r.1.1) hpq
    · apply b.apply_injective
        ((mem_labelPullback b E p.1).mp p.2).choose
        ((mem_labelPullback b E q.1).mp q.2).choose
      exact congrArg (fun r ↦ r.1.2) hpq
  have hcard := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_coe] using hcard

/-- A defect for the new label families is a defect for the old ones, a source
point where the source labels differ, or the pullback of a target point where the
target labels differ. -/
theorem equivarianceDefect_congr_subset {L : Type*} [Fintype L] [DecidableEq L]
    (b : FinitePartialBijection Y Z)
    (actY actY' : L → Equiv.Perm Y) (actZ actZ' : L → Equiv.Perm Z) :
    b.equivarianceDefect actY' actZ' ⊆
      b.equivarianceDefect actY actZ ∪ labelDisagreement actY' actY ∪
        b.labelPullback (labelDisagreement actZ' actZ) := by
  intro p hp
  by_cases hY : p ∈ labelDisagreement actY' actY
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hY)
  by_cases hZ : p ∈ b.labelPullback (labelDisagreement actZ' actZ)
  · exact Finset.mem_union_right _ hZ
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  have hY' : actY' p.1 p.2 = actY p.1 p.2 := by
    by_contra hne
    exact hY ((mem_labelDisagreement actY' actY p).mpr hne)
  rw [mem_equivarianceDefect] at hp ⊢
  intro hx hsx
  have hZ' : actZ' p.1 (b.apply p.2 hx) = actZ p.1 (b.apply p.2 hx) := by
    by_contra hne
    exact hZ ((mem_labelPullback b _ p).mpr
      ⟨hx, (mem_labelDisagreement actZ' actZ (p.1, b.apply p.2 hx)).mpr hne⟩)
  have hsx' : actY' p.1 p.2 ∈ b.source := by
    rw [hY']
    exact hsx
  intro heq
  apply hp hx hsx'
  calc b.apply (actY' p.1 p.2) hsx' = b.apply (actY p.1 p.2) hsx :=
        b.apply_eq_of_eq hY' hsx' hsx
    _ = actZ p.1 (b.apply p.2 hx) := heq
    _ = actZ' p.1 (b.apply p.2 hx) := hZ'.symm

/-- **Changing label families.**  The defect for new label families exceeds the
defect for old ones by at most the numbers of labelled source and target points
where the families differ. -/
theorem card_equivarianceDefect_congr_le {L : Type*} [Fintype L] [DecidableEq L]
    (b : FinitePartialBijection Y Z)
    (actY actY' : L → Equiv.Perm Y) (actZ actZ' : L → Equiv.Perm Z) :
    (b.equivarianceDefect actY' actZ').card ≤
      (b.equivarianceDefect actY actZ).card + (labelDisagreement actY' actY).card +
        (labelDisagreement actZ' actZ).card := by
  have hsub := Finset.card_le_card (equivarianceDefect_congr_subset b actY actY' actZ actZ')
  have h₁ := Finset.card_union_le (b.equivarianceDefect actY actZ ∪
    labelDisagreement actY' actY) (b.labelPullback (labelDisagreement actZ' actZ))
  have h₂ := Finset.card_union_le (b.equivarianceDefect actY actZ)
    (labelDisagreement actY' actY)
  have h₃ := card_labelPullback_le b (labelDisagreement actZ' actZ)
  omega

end FinitePartialBijection
end GroupApproximation
