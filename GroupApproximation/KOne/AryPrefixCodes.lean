import GroupApproximation.Leavitt.AryWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Prefix codes over a complete matrix family

The binary pencil elimination works over mixed-depth complete prefix codes of the binary
Leavitt family: `Leavitt/PrefixCode.lean` (the code structure and its orthogonality),
`KOne/CodePairTransport.lean` (matrix data indexed by two codes multiplies like
matrices), `KOne/EntryStrip.lean` (two-sided strips recover entries), and the
single-word split and index transport of `KOne/CodeChangeGlue.lean` and
`KOne/CompleteCodeSupply.lean`.  This module is all of that over a complete matrix
family `F` on an arbitrary alphabet `ι`.

The only arity-visible change is the split: a word is replaced by its `|ι|` children,
so the split family is indexed by `ι ⊕ {j // j ≠ j₀}` where the binary one used
`Fin 2 ⊕ {j // j ≠ j₀}`, and the size grows by `|ι| - 1`.
-/

namespace GroupApproximation

/-- An ordered prefix code over an alphabet `α`, indexed by `κ`: pairwise incomparable
words. -/
structure AryPrefixCode (κ : Type*) (α : Type*) where
  word : κ → List α
  prefix_free : ∀ ⦃i j⦄, i ≠ j → ¬ word i <+: word j

/-- Prefix comparison against a one-letter extension. -/
theorem incomparable_append_single_ary {α : Type*} {v w : List α}
    (hvw : ¬v <+: w) (hwv : ¬w <+: v) (z : α) :
    ¬v <+: w ++ [z] ∧ ¬w ++ [z] <+: v := by
  constructor
  · intro h
    by_cases hlen : v.length ≤ w.length
    · exact hvw (List.prefix_of_prefix_length_le h
        (List.prefix_append w [z]) hlen)
    · have hlen2 : v.length = (w ++ [z]).length := by
        have h1 := h.length_le
        simp only [List.length_append, List.length_singleton] at h1 ⊢
        omega
      have heq := h.eq_of_length hlen2
      refine hwv ?_
      rw [heq]
      exact List.prefix_append w [z]
  · intro h
    exact hwv ((List.prefix_append w [z]).trans h)

/-- **The split family**: replacing the word at one index of a prefix family by all of
its one-letter children (indexed by `α ⊕ (everything else)`) is again a prefix family. -/
theorem split_family_free_ary {α κ : Type*} (τ : κ → List α)
    (hfree : ∀ ⦃i j : κ⦄, i ≠ j → ¬τ i <+: τ j) (j₀ : κ) :
    ∀ ⦃p q : α ⊕ {i : κ // i ≠ j₀}⦄, p ≠ q →
      ¬(Sum.elim (fun z ↦ τ j₀ ++ [z]) (fun i ↦ τ i.1)) p <+:
        (Sum.elim (fun z ↦ τ j₀ ++ [z]) (fun i ↦ τ i.1)) q := by
  rintro (z₁ | i₁) (z₂ | i₂) hne h
  · have hz : z₁ ≠ z₂ := fun hz ↦ hne (by rw [hz])
    have hlen : (τ j₀ ++ [z₁]).length = (τ j₀ ++ [z₂]).length := by
      simp
    have heq := h.eq_of_length hlen
    have : z₁ = z₂ := by
      have := List.append_inj_right heq rfl
      simpa using this
    exact hz this
  · have hinc := incomparable_append_single_ary
      (hfree i₂.2) (hfree (Ne.symm i₂.2)) z₁
    exact hinc.2 h
  · have hinc := incomparable_append_single_ary
      (hfree i₁.2) (hfree (Ne.symm i₁.2)) z₂
    exact hinc.1 h
  · have hne' : i₁.1 ≠ i₂.1 := fun hh ↦
      hne (congrArg Sum.inr (Subtype.ext hh))
    exact hfree hne' h

namespace AryPrefixCode

/-- The code with the word at `j₀` replaced by its one-letter children. -/
def split {κ α : Type*} (C : AryPrefixCode κ α) (j₀ : κ) :
    AryPrefixCode (α ⊕ {j : κ // j ≠ j₀}) α :=
  ⟨Sum.elim (fun z ↦ C.word j₀ ++ [z]) (fun q ↦ C.word q.1),
    split_family_free_ary C.word C.prefix_free j₀⟩

@[simp] theorem split_word_inl {κ α : Type*} (C : AryPrefixCode κ α) (j₀ : κ) (z : α) :
    (C.split j₀).word (Sum.inl z) = C.word j₀ ++ [z] := rfl

@[simp] theorem split_word_inr {κ α : Type*} (C : AryPrefixCode κ α) (j₀ : κ)
    (q : {j : κ // j ≠ j₀}) :
    (C.split j₀).word (Sum.inr q) = C.word q.1 := rfl

/-- Reindexing a prefix code along an equivalence. -/
def reindex {κ κ' α : Type*} (C : AryPrefixCode κ α) (e : κ' ≃ κ) : AryPrefixCode κ' α :=
  ⟨C.word ∘ e, fun _ _ hpq ↦ C.prefix_free (fun h ↦ hpq (e.injective h))⟩

@[simp] theorem reindex_word {κ κ' α : Type*} (C : AryPrefixCode κ α) (e : κ' ≃ κ) (p : κ') :
    (C.reindex e).word p = C.word (e p) := rfl

end AryPrefixCode

namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- `s`-words are nonzero in a nontrivial ring. -/
theorem wordS_ne_zero [Nontrivial A] (a : List ι) : F.wordS a ≠ 0 := by
  intro h
  have h1 : F.wordT a * F.wordS a = 1 := F.wordT_mul_wordS_self a
  rw [h, mul_zero] at h1
  exact zero_ne_one h1

/-- The orthogonality relations of a prefix code. -/
theorem prefixCode_orthogonal {κ : Type*} [DecidableEq κ] (E : AryPrefixCode κ ι)
    (i j : κ) :
    F.wordT (E.word i) * F.wordS (E.word j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact F.wordT_mul_wordS_self _
  · rw [if_neg hij]
    exact F.wordT_mul_wordS_of_incomparable _ _ (E.prefix_free hij)
      (E.prefix_free (Ne.symm hij))

/-- A prefix code is *complete* when its cylinders sum to `1`. -/
def IsComplete {κ : Type*} [Fintype κ] (E : AryPrefixCode κ ι) : Prop :=
  ∑ i, F.cylinder (E.word i) = 1

/-- A complete prefix code is a complete matrix family. -/
def codeFamily {κ : Type*} [Fintype κ] [DecidableEq κ] (E : AryPrefixCode κ ι)
    (hE : F.IsComplete E) : CompleteMatrixFamily A κ where
  left i := F.wordS (E.word i)
  right i := F.wordT (E.word i)
  orthogonal := F.prefixCode_orthogonal E
  complete := hE

@[simp] theorem codeFamily_left {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : AryPrefixCode κ ι) (hE : F.IsComplete E) (i : κ) :
    (F.codeFamily E hE).left i = F.wordS (E.word i) := rfl

@[simp] theorem codeFamily_right {κ : Type*} [Fintype κ] [DecidableEq κ]
    (E : AryPrefixCode κ ι) (hE : F.IsComplete E) (i : κ) :
    (F.codeFamily E hE).right i = F.wordT (E.word i) := rfl

/-- The split code is complete when the code is. -/
theorem split_isComplete {κ : Type*} [Fintype κ] [DecidableEq κ]
    (C : AryPrefixCode κ ι) (hC : F.IsComplete C) (j₀ : κ) :
    F.IsComplete (C.split j₀) := by
  classical
  unfold IsComplete
  rw [Fintype.sum_sum_type]
  have h1 : ∑ z : ι, F.cylinder (C.word j₀ ++ [z]) = F.cylinder (C.word j₀) :=
    (F.cylinder_split (C.word j₀)).symm
  have h2 : ∑ i : {i : κ // i ≠ j₀}, F.cylinder (C.word i.1) =
      ∑ i ∈ Finset.univ.erase j₀, F.cylinder (C.word i) :=
    (Finset.sum_subtype (Finset.univ.erase j₀)
      (fun x ↦ by simp [Finset.mem_erase]) (fun i ↦ F.cylinder (C.word i))).symm
  simp only [AryPrefixCode.split_word_inl, AryPrefixCode.split_word_inr]
  rw [h1, h2, Finset.add_sum_erase _ (fun i ↦ F.cylinder (C.word i))
    (Finset.mem_univ j₀)]
  exact hC

/-- Completeness transports along an index equivalence. -/
theorem reindex_isComplete {κ κ' : Type*} [Fintype κ] [Fintype κ']
    (C : AryPrefixCode κ ι) (hC : F.IsComplete C) (e : κ' ≃ κ) :
    F.IsComplete (C.reindex e) := by
  unfold IsComplete
  rw [Fintype.sum_equiv e (fun p ↦ F.cylinder ((C.reindex e).word p))
    (fun i ↦ F.cylinder (C.word i)) (fun p ↦ rfl)]
  exact hC

/-! ### Transport along a pair of complete prefix codes -/

section Transport

variable {ρ κ μ : Type*} [Fintype ρ] [Fintype κ] [Fintype μ]

/-- **Code-pair product collapse**: only the middle code's orthogonality is used. -/
theorem codePair_mul [DecidableEq κ] (C : AryPrefixCode κ ι)
    (R : ρ → List ι) (W : μ → List ι) (E : ρ → κ → A) (G : κ → μ → A) :
    (∑ i, ∑ j, F.wordS (R i) * E i j * F.wordT (C.word j)) *
      (∑ j, ∑ l, F.wordS (C.word j) * G j l * F.wordT (W l)) =
    ∑ i, ∑ l, F.wordS (R i) * (∑ j, E i j * G j l) * F.wordT (W l) := by
  classical
  have hterm : ∀ (i : ρ) (j j' : κ) (l : μ),
      F.wordS (R i) * E i j * F.wordT (C.word j) *
        (F.wordS (C.word j') * G j' l * F.wordT (W l)) =
      if j = j' then F.wordS (R i) * (E i j * G j' l) * F.wordT (W l)
        else 0 := by
    intro i j j' l
    rw [show F.wordS (R i) * E i j * F.wordT (C.word j) *
        (F.wordS (C.word j') * G j' l * F.wordT (W l)) =
      F.wordS (R i) * E i j * (F.wordT (C.word j) * F.wordS (C.word j')) *
        (G j' l * F.wordT (W l)) from by noncomm_ring,
      F.prefixCode_orthogonal C j j']
    split_ifs with hjj
    · rw [mul_one]
      noncomm_ring
    · rw [mul_zero, zero_mul]
  calc (∑ i, ∑ j, F.wordS (R i) * E i j * F.wordT (C.word j)) *
        (∑ j, ∑ l, F.wordS (C.word j) * G j l * F.wordT (W l))
      = ∑ i, ∑ j, ∑ j', ∑ l,
          F.wordS (R i) * E i j * F.wordT (C.word j) *
            (F.wordS (C.word j') * G j' l * F.wordT (W l)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j' _ ↦ ?_
        rw [Finset.mul_sum]
    _ = ∑ i, ∑ j, ∑ j', ∑ l,
          (if j = j' then
            F.wordS (R i) * (E i j * G j' l) * F.wordT (W l) else 0) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl
          fun j _ ↦ Finset.sum_congr rfl fun j' _ ↦
          Finset.sum_congr rfl fun l _ ↦ hterm i j j' l
    _ = ∑ i, ∑ j, ∑ l,
          F.wordS (R i) * (E i j * G j l) * F.wordT (W l) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ j)]
    _ = ∑ i, ∑ l, F.wordS (R i) * (∑ j, E i j * G j l) *
          F.wordT (W l) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]

/-- **Rectangular inverse pairs transport to `1`** along complete codes. -/
theorem codePair_mul_eq_one [DecidableEq ρ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (hR : F.IsComplete R) (C : AryPrefixCode κ ι)
    (E : ρ → κ → A) (G : κ → ρ → A)
    (hEG : ∀ i i', ∑ j, E i j * G j i' = if i = i' then (1 : A) else 0) :
    (∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
      (∑ j, ∑ i, F.wordS (C.word j) * G j i * F.wordT (R.word i)) = 1 := by
  classical
  rw [F.codePair_mul C R.word R.word E G]
  calc ∑ i, ∑ i', F.wordS (R.word i) * (∑ j, E i j * G j i') *
        F.wordT (R.word i')
      = ∑ i, ∑ i', (if i = i' then
          F.wordS (R.word i) * F.wordT (R.word i') else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦
          Finset.sum_congr rfl fun i' _ ↦ ?_
        rw [hEG i i']
        simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    _ = ∑ i, F.wordS (R.word i) * F.wordT (R.word i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
    _ = 1 := hR

/-- The transported unit of a rectangular two-sided-invertible `A`-matrix along a pair
of complete codes. -/
def codePairUnit [DecidableEq ρ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (hR : F.IsComplete R)
    (C : AryPrefixCode κ ι) (hC : F.IsComplete C)
    (E : ρ → κ → A) (G : κ → ρ → A)
    (hEG : ∀ i i', ∑ j, E i j * G j i' = if i = i' then (1 : A) else 0)
    (hGE : ∀ j j', ∑ i, G j i * E i j' = if j = j' then (1 : A) else 0) : Aˣ where
  val := ∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)
  inv := ∑ j, ∑ i, F.wordS (C.word j) * G j i * F.wordT (R.word i)
  val_inv := F.codePair_mul_eq_one R hR C E G hEG
  inv_val := F.codePair_mul_eq_one C hC R G E hGE

@[simp] theorem codePairUnit_val [DecidableEq ρ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (hR : F.IsComplete R)
    (C : AryPrefixCode κ ι) (hC : F.IsComplete C)
    (E : ρ → κ → A) (G : κ → ρ → A) (hEG) (hGE) :
    ((F.codePairUnit R hR C hC E G hEG hGE : Aˣ) : A) =
      ∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j) := rfl

/-! ### Entry strips -/

/-- Two-sided strips of a code pencil recover the entries. -/
theorem wordT_pencilVal_wordS [DecidableEq ρ] [DecidableEq κ]
    (R : AryPrefixCode ρ ι) (C : AryPrefixCode κ ι)
    (E : ρ → κ → A) (i₀ : ρ) (j₀ : κ) :
    F.wordT (R.word i₀) *
      (∑ i, ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
      F.wordS (C.word j₀) = E i₀ j₀ := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul]
  calc ∑ i, (F.wordT (R.word i₀) *
        ∑ j, F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
        F.wordS (C.word j₀)
      = ∑ i, (if i₀ = i then
          ∑ j, (if j = j₀ then E i j else 0) else 0) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        calc ∑ j, F.wordT (R.word i₀) *
              (F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
              F.wordS (C.word j₀)
            = ∑ j, (if i₀ = i then
                (if j = j₀ then E i j else 0) else 0) := by
              refine Finset.sum_congr rfl fun j _ ↦ ?_
              rw [show F.wordT (R.word i₀) *
                  (F.wordS (R.word i) * E i j * F.wordT (C.word j)) *
                  F.wordS (C.word j₀) =
                (F.wordT (R.word i₀) * F.wordS (R.word i)) * E i j *
                  (F.wordT (C.word j) * F.wordS (C.word j₀)) from by
                  noncomm_ring,
                F.prefixCode_orthogonal R i₀ i,
                F.prefixCode_orthogonal C j j₀]
              by_cases h1 : i₀ = i <;> by_cases h2 : j = j₀
              · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, one_mul, mul_one]
              · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2, mul_zero]
              · rw [if_neg h1, if_pos h2, if_neg h1, zero_mul, zero_mul]
              · rw [if_neg h1, if_neg h2, if_neg h1, zero_mul, zero_mul]
          _ = (if i₀ = i then
              ∑ j, (if j = j₀ then E i j else 0) else 0) := by
            split_ifs with h1
            · rfl
            · exact Finset.sum_const_zero
    _ = ∑ j, (if j = j₀ then E i₀ j else 0) := by
        rw [Finset.sum_ite_eq Finset.univ i₀, if_pos (Finset.mem_univ i₀)]
    _ = E i₀ j₀ := by
        rw [Finset.sum_ite_eq' Finset.univ j₀, if_pos (Finset.mem_univ j₀)]

/-- A product strips through the insertion of a complete code. -/
theorem strip_insert (C : AryPrefixCode κ ι) (hC : F.IsComplete C)
    (x y : A) (w w' : List ι) :
    F.wordT w * (x * y) * F.wordS w' =
      ∑ j, (F.wordT w * x * F.wordS (C.word j)) *
        (F.wordT (C.word j) * y * F.wordS w') := by
  have hxy : x * y = x * (∑ j, F.wordS (C.word j) * F.wordT (C.word j)) * y := by
    rw [show (∑ j, F.wordS (C.word j) * F.wordT (C.word j)) = 1 from hC, mul_one]
  rw [hxy, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  noncomm_ring

end Transport

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.split_family_free_ary
#audit_axioms GroupApproximation.CompleteMatrixFamily.split_isComplete
#audit_axioms GroupApproximation.CompleteMatrixFamily.reindex_isComplete
#audit_axioms GroupApproximation.CompleteMatrixFamily.codePair_mul
#audit_axioms GroupApproximation.CompleteMatrixFamily.codePair_mul_eq_one
#audit_axioms GroupApproximation.CompleteMatrixFamily.wordT_pencilVal_wordS
#audit_axioms GroupApproximation.CompleteMatrixFamily.strip_insert
