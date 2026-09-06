import GroupApproximation.CharClass.LemmaTwoParity

/-!
# `V = 𝟏³ ⊕ H` as a pointwise sum of lines

Lane `cc-lix-odd`, for `cc-steenrod`'s split relation.

`splitRelation_of_sum` consumes a bundle presented as a pointwise sum of rank-one
projections, together with the rank in the `Bundle.rank` form rather than as a trace.  This
file supplies both for `V`.

## The multiplicity, which is the whole content

`HBlk dd` is `Σ j, Fin (dd j)`, so it is indexed by **pairs**, and `Hmat` is block-diagonal
with the block at `(j, i)` equal to `m.2 j` for **every** `i`.  So the tautological line of
the `j`-th projective factor appears with multiplicity `dd j`, not once.  Three constant
lines and `∑ⱼ dⱼ` tautological ones make `3 + ∑ⱼ dⱼ = lixRank dd`.

A decomposition indexed one line per factor would be the wrong shape and would fail only
several files downstream, in the value of the slice class.

## Main results

* `vLine` — the family, indexed by `Fin 3 ⊕ HBlk dd`.
* `trace_vLine` — each line has trace one.
* `Vmat_eq_sum_lines` — **the pointwise sum**.

The rank in `Bundle.rank` form follows from `trace_Vmat` through `Bundle.trace_eq_rank`;
it is deferred to a follow-up so that the decomposition, which is what `cc-steenrod` is
blocked on, lands on its own.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-! ## 1. The lines -/

/-- The `i`-th constant line of the trivial summand. -/
def trivLine (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a c => if a = i ∧ c = i then 1 else 0

/-- The tautological line sitting in the block `b`. -/
def hLine (b : HBlk dd) (m : baseM dd) : Matrix (HIdx dd) (HIdx dd) ℂ :=
  Matrix.blockDiagonal' fun b' : HBlk dd =>
    if b' = b then ((m.2 b'.1 : CP (dd b'.1)) :
      Matrix (Fin (dd b'.1 + 1)) (Fin (dd b'.1 + 1)) ℂ) else 0

/-- **The family of lines of `V`**, indexed by `Fin 3 ⊕ HBlk dd`, whose cardinality is
`lixRank dd`. -/
def vLine (b : Fin 3 ⊕ HBlk dd) (m : baseM dd) : Matrix (VIdx dd) (VIdx dd) ℂ :=
  match b with
  | Sum.inl i => Matrix.fromBlocks (trivLine i) 0 0 0
  | Sum.inr b => Matrix.fromBlocks 0 0 0 (hLine b m)

/-! ## 2. Each line has trace one -/

theorem trace_trivLine (i : Fin 3) : Matrix.trace (trivLine i) = 1 := by
  rw [Matrix.trace]
  simp [Matrix.diag, trivLine]

theorem trace_hLine (b : HBlk dd) (m : baseM dd) : Matrix.trace (hLine b m) = 1 := by
  rw [hLine, Matrix.trace_blockDiagonal']
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    exact AlgTop.CPn.trace_coe (m.2 b.1)
  · intro b' _ hne
    rw [if_neg hne, Matrix.trace_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem trace_vLine (b : Fin 3 ⊕ HBlk dd) (m : baseM dd) :
    Matrix.trace (vLine b m) = 1 := by
  cases b with
  | inl i => rw [vLine, trace_fromBlocks_gen, trace_trivLine, Matrix.trace_zero, add_zero]
  | inr b => rw [vLine, trace_fromBlocks_gen, Matrix.trace_zero, trace_hLine, zero_add]

/-! ## 3. The pointwise sum -/

theorem sum_trivLine : (∑ i : Fin 3, trivLine i) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext a c
  rw [Matrix.sum_apply]
  simp only [trivLine, Matrix.one_apply]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro i _ hne
      exact if_neg fun hh => hne hh.1.symm
    · intro hc
      exact absurd (Finset.mem_univ a) hc
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun i _ => ?_
    exact if_neg fun hh => h (hh.1.trans hh.2.symm)

theorem sum_hLine (m : baseM dd) :
    (∑ b : HBlk dd, hLine b m) = Hmat m := by
  ext p q
  obtain ⟨b₁, i⟩ := p
  obtain ⟨b₂, jj⟩ := q
  rw [Matrix.sum_apply]
  by_cases h : b₁ = b₂
  · subst h
    rw [Hmat, Matrix.blockDiagonal'_apply_eq]
    rw [Finset.sum_eq_single b₁]
    · rw [hLine, Matrix.blockDiagonal'_apply_eq, if_pos rfl]
    · intro b' _ hne
      rw [hLine, Matrix.blockDiagonal'_apply_eq, if_neg (Ne.symm hne)]
      rfl
    · intro hc
      exact absurd (Finset.mem_univ b₁) hc
  · rw [Hmat, Matrix.blockDiagonal'_apply_ne _ _ _ h]
    refine Finset.sum_eq_zero fun b' _ => ?_
    rw [hLine, Matrix.blockDiagonal'_apply_ne _ _ _ h]

/-- **`V` is the pointwise sum of its lines.** -/
theorem Vmat_eq_sum_lines (m : baseM dd) :
    Vmat m = ∑ b : Fin 3 ⊕ HBlk dd, vLine b m := by
  rw [Fintype.sum_sum_type]
  ext p q
  rw [Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply, Vmat]
  cases p with
  | inl a =>
      cases q with
      | inl c =>
          rw [Matrix.fromBlocks_apply₁₁]
          have hz : ∀ b : HBlk dd, vLine (Sum.inr b) m (Sum.inl a) (Sum.inl c) = 0 :=
            fun _ => rfl
          rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hz b,
            Finset.sum_const_zero, add_zero]
          have hv : ∀ i : Fin 3,
              vLine (Sum.inl i) m (Sum.inl a) (Sum.inl c) = trivLine i a c := fun _ => rfl
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hv i]
          rw [← Matrix.sum_apply, sum_trivLine]
      | inr c =>
          simp [vLine]
  | inr a =>
      cases q with
      | inl c =>
          simp [vLine]
      | inr c =>
          rw [Matrix.fromBlocks_apply₂₂]
          have hz : ∀ i : Fin 3, vLine (Sum.inl i) m (Sum.inr a) (Sum.inr c) = 0 :=
            fun _ => rfl
          rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hz i,
            Finset.sum_const_zero, zero_add]
          have hv : ∀ b : HBlk dd,
              vLine (Sum.inr b) m (Sum.inr a) (Sum.inr c) = hLine b m a c := fun _ => rfl
          rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hv b]
          rw [← Matrix.sum_apply, sum_hLine]

end GroupApproximation.CharClass
