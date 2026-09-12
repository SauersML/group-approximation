import GroupApproximation.KunThom.ComponentCountingRelativeFunctorDefects

/-!
# Equivariance of partial bijections along words of labels

In the proof of Kun–Thom Lemma 4.3 (arXiv:2608.06222), a compressor `t`
conjugates a generator `s` of `Γ` to `t s t⁻¹ ∈ Γ`.  That element is represented
by a word `w_s` in the generators.  An allowed arrow `b` has small defect for
the generator labels, and it must be commuted past the word action.  Kun and
Thom bound the cost by `|w_s|` times the generator defect.

* `wordAct act w`: the permutation of the word `w`, read as a left-to-right
  product of letters.
* `wordDefect b actY actZ w`: the source points where `b` fails to intertwine
  the two word actions.
* `card_wordDefect_le`: `#wordDefect ≤ sourceDefect + |w| · #defect(b)`.
* `card_equivarianceDefect_wordAct_le`: the same bound for a finite family of
  words, summed over the family.
-/

namespace GroupApproximation
namespace FinitePartialBijection

variable {Y Z : FiniteModel}

/-- The permutation of a word of labels: the left-to-right product of its letters. -/
def wordAct {L : Type*} (act : L → Equiv.Perm Y) : List L → Equiv.Perm Y
  | [] => 1
  | l :: w => act l * wordAct act w

@[simp] theorem wordAct_nil {L : Type*} (act : L → Equiv.Perm Y) :
    wordAct act [] = 1 :=
  rfl

@[simp] theorem wordAct_cons {L : Type*} (act : L → Equiv.Perm Y) (l : L) (w : List L) :
    wordAct act (l :: w) = act l * wordAct act w :=
  rfl

/-- Source points where a partial bijection fails to intertwine the actions of one
word, counting every point for which the comparison is not available. -/
noncomputable def wordDefect {L : Type*} (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) (w : List L) : Finset Y := by
  classical
  exact Finset.univ.filter fun y ↦
    ∀ hy : y ∈ b.source, ∀ hwy : wordAct actY w y ∈ b.source,
      b.apply (wordAct actY w y) hwy ≠ wordAct actZ w (b.apply y hy)

@[simp] theorem mem_wordDefect {L : Type*} (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) (w : List L) (y : Y) :
    y ∈ b.wordDefect actY actZ w ↔
      ∀ hy : y ∈ b.source, ∀ hwy : wordAct actY w y ∈ b.source,
        b.apply (wordAct actY w y) hwy ≠ wordAct actZ w (b.apply y hy) := by
  classical
  simp [wordDefect]

/-- For the empty word the only defects are points outside the source. -/
theorem card_wordDefect_nil_le {L : Type*} (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) :
    (b.wordDefect actY actZ []).card ≤ b.sourceDefect := by
  have hsub : b.wordDefect actY actZ [] ⊆ Finset.univ \ b.source := by
    intro y hy
    rw [mem_wordDefect] at hy
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ _, fun hs ↦ hy hs hs rfl⟩
  have hcard := Finset.card_le_card hsub
  have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b.source)
  rw [Finset.card_univ] at hsplit
  unfold sourceDefect
  omega

/-- A defect of the word `l :: w` is a defect of `w`, or a defect of the letter `l`
at the image of the point under `w`. -/
theorem wordDefect_cons_subset {L : Type*} [Fintype L] [DecidableEq L]
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) (l : L) (w : List L) :
    b.wordDefect actY actZ (l :: w) ⊆
      b.wordDefect actY actZ w ∪
        Finset.univ.filter fun y ↦ (l, wordAct actY w y) ∈ b.equivarianceDefect actY actZ := by
  intro y hy
  by_cases h₁ : y ∈ b.wordDefect actY actZ w
  · exact Finset.mem_union_left _ h₁
  by_cases h₃ : (l, wordAct actY w y) ∈ b.equivarianceDefect actY actZ
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₃⟩)
  exfalso
  rw [mem_wordDefect] at hy h₁
  rw [mem_equivarianceDefect] at h₃
  push Not at h₁ h₃
  obtain ⟨hy', hz, hzeq⟩ := h₁
  obtain ⟨hz', hsz, hseq⟩ := h₃
  apply hy hy' hsz
  calc b.apply (wordAct actY (l :: w) y) hsz
      = b.apply (actY l (wordAct actY w y)) hsz := rfl
    _ = actZ l (b.apply (wordAct actY w y) hz') := hseq
    _ = actZ l (b.apply (wordAct actY w y) hz) := rfl
    _ = actZ l (wordAct actZ w (b.apply y hy')) := by rw [hzeq]
    _ = wordAct actZ (l :: w) (b.apply y hy') := rfl

/-- Appending a letter adds at most the letter defects of `b`. -/
theorem card_wordDefect_cons_le {L : Type*} [Fintype L] [DecidableEq L]
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) (l : L) (w : List L) :
    (b.wordDefect actY actZ (l :: w)).card ≤
      (b.wordDefect actY actZ w).card + (b.equivarianceDefect actY actZ).card := by
  have hinj : (Finset.univ.filter fun y ↦
      (l, wordAct actY w y) ∈ b.equivarianceDefect actY actZ).card ≤
        (b.equivarianceDefect actY actZ).card := by
    apply Finset.card_le_card_of_injOn (fun y ↦ (l, wordAct actY w y))
    · intro y hy
      rw [Finset.mem_coe] at hy ⊢
      exact (Finset.mem_filter.mp hy).2
    · intro y _ y' _ hyy'
      exact (wordAct actY w).injective (congrArg Prod.snd hyy')
  have h₁ := Finset.card_le_card (wordDefect_cons_subset b actY actZ l w)
  have h₂ := Finset.card_union_le (b.wordDefect actY actZ w)
    (Finset.univ.filter fun y ↦ (l, wordAct actY w y) ∈ b.equivarianceDefect actY actZ)
  omega

/-- **Commuting past a word.**  The defect of `b` for the action of a word is at
most its missing source mass plus the word length times its letter defect. -/
theorem card_wordDefect_le {L : Type*} [Fintype L] [DecidableEq L]
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) (w : List L) :
    (b.wordDefect actY actZ w).card ≤
      b.sourceDefect + w.length * (b.equivarianceDefect actY actZ).card := by
  induction w with
  | nil =>
    have h := card_wordDefect_nil_le b actY actZ
    simp only [List.length_nil, zero_mul, add_zero]
    exact h
  | cons l w ih =>
    have h := card_wordDefect_cons_le b actY actZ l w
    rw [List.length_cons, add_mul, one_mul]
    omega

/-- **Word labels.**  For a finite family of words of length at most `k`, the
defect of `b` for the word actions is at most the family size times
`sourceDefect + k · #defect(b)`. -/
theorem card_equivarianceDefect_wordAct_le {L L' : Type*} [Fintype L] [DecidableEq L]
    [Fintype L'] [DecidableEq L']
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z)
    (w : L' → List L) {k : ℕ} (hk : ∀ l', (w l').length ≤ k) :
    (b.equivarianceDefect (fun l' ↦ wordAct actY (w l'))
        (fun l' ↦ wordAct actZ (w l'))).card ≤
      Fintype.card L' * (b.sourceDefect + k * (b.equivarianceDefect actY actZ).card) := by
  have hsub : b.equivarianceDefect (fun l' ↦ wordAct actY (w l'))
      (fun l' ↦ wordAct actZ (w l')) ⊆
        Finset.univ.biUnion fun l' ↦
          (b.wordDefect actY actZ (w l')).image fun y ↦ (l', y) := by
    intro p hp
    rw [Finset.mem_biUnion]
    refine ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, ?_, rfl⟩⟩
    rw [mem_equivarianceDefect] at hp
    exact (mem_wordDefect b actY actZ (w p.1) p.2).mpr hp
  calc (b.equivarianceDefect (fun l' ↦ wordAct actY (w l'))
        (fun l' ↦ wordAct actZ (w l'))).card
      ≤ (Finset.univ.biUnion fun l' ↦
          (b.wordDefect actY actZ (w l')).image fun y ↦ (l', y)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ l' : L', ((b.wordDefect actY actZ (w l')).image fun y ↦ (l', y)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _l' : L', (b.sourceDefect + k * (b.equivarianceDefect actY actZ).card) := by
        refine Finset.sum_le_sum fun l' _ ↦ ?_
        have hw := card_wordDefect_le b actY actZ (w l')
        have hl := Nat.mul_le_mul_right (b.equivarianceDefect actY actZ).card (hk l')
        have himage := Finset.card_image_le (s := b.wordDefect actY actZ (w l'))
          (f := fun y ↦ (l', y))
        omega
    _ = Fintype.card L' * (b.sourceDefect + k * (b.equivarianceDefect actY actZ).card) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end FinitePartialBijection
end GroupApproximation
