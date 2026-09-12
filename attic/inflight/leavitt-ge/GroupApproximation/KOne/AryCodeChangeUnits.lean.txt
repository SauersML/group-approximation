import GroupApproximation.KOne.AryPrefixCodes
import GroupApproximation.KOne.FieldMatrixReduction
import GroupApproximation.Meta.AxiomGuard

/-!
# Code-change units at arbitrary arity

For two complete prefix codes `τ`, `σ` on the same index type, the code-change unit
`Ω = Σⱼ s_{τⱼ} t_{σⱼ}` lies in `centralClassGroup A`.  This is the Higman--Thompson
generation step of the pencil elimination (`KOne/CodeChangeUnits.lean` at arity two,
where the receptacle is `stableUnits`).  At arity `d` the receptacle has to be
`centralClassGroup`: a transposition of two cylinders at depth one is a permutation
matrix of sign `-1`, whose `K₁`-class is the scalar class of `-1`, nontrivial as soon as
`-1` is not a `(d-1)`-st power.

The proof is shorter than the binary one because the alignment of targets needs no
transposition calculus:

* **Permutation units are scalar moves.**  For a complete code `τ` and a permutation `π`
  of its index type, `Σⱼ s_{τ(π j)} t_{τ j}` is the image of a permutation matrix under
  the complete family `F.codeFamily τ`, so it lies in `centralClassGroup A` by
  `CompleteMatrixFamily.unitsEquiv_field_matrix_mem_centralClassGroup` (`permUnit_mem`).
* **Sibling groups at maximal depth.**  A complete code of size at least two contains all
  `|ι|` children `w ++ [z]` of some word `w` (`exists_sibling_group`).
* **Merge.**  If the source children `σ(g z) = w ++ [z]` are paired with the target children
  `v ++ [z]`, the sum of those `|ι|` terms is `s_v t_w`, and replacing the group by the one
  pair `(v, w)` gives a code change between two smaller complete codes.  A permutation unit
  aligns the targets first (`exists_perm_extending`).

Induction on the size then gives `codeChange_mem_centralClassGroup`.
-/

universe uκ

namespace GroupApproximation
namespace CompleteMatrixFamily

open MatrixDiagonalization

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-! ### Two word facts -/

/-- Over an alphabet with two letters, a word whose cylinder is `1` is empty. -/
theorem eq_nil_of_cylinder_eq_one [Nontrivial A] [Nontrivial ι] {w : List ι}
    (h : F.cylinder w = 1) : w = [] := by
  cases w with
  | nil => rfl
  | cons i rest =>
      exfalso
      obtain ⟨j, hij⟩ := exists_ne i
      have hinc₁ : ¬(i :: rest) <+: [j] := by
        intro hp
        rw [List.cons_prefix_cons] at hp
        exact hij hp.1.symm
      have hinc₂ : ¬[j] <+: (i :: rest) := by
        intro hp
        rw [List.cons_prefix_cons] at hp
        exact hij hp.1
      have hzero : F.wordS [j] = 0 := by
        have h1 : F.cylinder (i :: rest) * F.wordS [j] = F.wordS [j] := by
          rw [h, one_mul]
        rw [cylinder, mul_assoc, F.wordT_mul_wordS_of_incomparable _ _ hinc₁ hinc₂,
          mul_zero] at h1
        exact h1.symm
      exact F.wordS_ne_zero [j] hzero

/-- **Sibling group at maximal depth**: a complete prefix code with at least two words
contains all one-letter children of some word. -/
theorem exists_sibling_group [Nontrivial A] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : AryPrefixCode κ ι) (hσ : F.IsComplete σ) (hcard : 2 ≤ Fintype.card κ) :
    ∃ (w : List ι) (g : ι → κ), ∀ z, σ.word (g z) = w ++ [z] := by
  classical
  have hne : (Finset.univ : Finset κ).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by omega)
  obtain ⟨j₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j ↦ (σ.word j).length) hne
  have hm_ne : σ.word j₀ ≠ [] := by
    intro hm
    obtain ⟨j₁, hj₁⟩ := Fintype.exists_ne_of_one_lt_card (by omega) j₀
    exact σ.prefix_free (Ne.symm hj₁) (by rw [hm]; exact List.nil_prefix)
  obtain ⟨w, a, hwa⟩ : ∃ (w : List ι) (a : ι), σ.word j₀ = w ++ [a] :=
    ⟨(σ.word j₀).dropLast, (σ.word j₀).getLast hm_ne,
      (List.dropLast_append_getLast hm_ne).symm⟩
  have hlen₀ : (σ.word j₀).length = w.length + 1 := by
    rw [hwa]
    simp
  have hcover : ∀ b : ι, ∃ j, σ.word j = w ++ [b] := by
    intro b
    have hsum : ∑ j, F.cylinder (σ.word j) * F.wordS (w ++ [b]) = F.wordS (w ++ [b]) := by
      rw [← Finset.sum_mul, show (∑ j, F.cylinder (σ.word j)) = 1 from hσ, one_mul]
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero
      (by rw [hsum]; exact F.wordS_ne_zero _)
    refine ⟨j, ?_⟩
    by_contra hneq
    apply hj
    by_cases h1 : σ.word j <+: w ++ [b]
    · exfalso
      have hlenj : (σ.word j).length ≤ w.length := by
        have h2 := h1.length_le
        have h3 : (σ.word j).length ≠ (w ++ [b]).length :=
          fun h ↦ hneq (h1.eq_of_length h)
        simp only [List.length_append, List.length_singleton] at h2 h3
        omega
      have hjw : σ.word j <+: w :=
        List.prefix_of_prefix_length_le h1 (List.prefix_append w [b]) hlenj
      have hjm : σ.word j <+: σ.word j₀ := by
        rw [hwa]
        exact hjw.trans (List.prefix_append w [a])
      have hjj₀ : j ≠ j₀ := by
        intro h
        rw [h, hlen₀] at hlenj
        omega
      exact σ.prefix_free hjj₀ hjm
    · by_cases h2 : w ++ [b] <+: σ.word j
      · exfalso
        apply hneq
        refine (h2.eq_of_length ?_).symm
        have h3 := h2.length_le
        have h4 := hmax j (Finset.mem_univ j)
        simp only [List.length_append, List.length_singleton] at h3 ⊢
        omega
      · rw [cylinder, mul_assoc, F.wordT_mul_wordS_of_incomparable _ _ h1 h2, mul_zero]
  choose g hg using hcover
  exact ⟨w, g, hg⟩

/-- A partial bijection between the images of two injections extends to a permutation. -/
theorem exists_perm_extending {κ α : Type*} [Fintype κ] [DecidableEq κ]
    (g h : α → κ) (hg : Function.Injective g) (hh : Function.Injective h) :
    ∃ π : Equiv.Perm κ, ∀ z, π (g z) = h z := by
  classical
  let e : {x // x ∈ Set.range g} ≃ {x // x ∈ Set.range h} :=
    (Equiv.ofInjective g hg).symm.trans (Equiv.ofInjective h hh)
  refine ⟨e.extendSubtype, fun z ↦ ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (g z) ⟨z, rfl⟩]
  have hsymm : (Equiv.ofInjective g hg).symm ⟨g z, ⟨z, rfl⟩⟩ = z :=
    hg (Equiv.apply_ofInjective_symm hg _)
  show h ((Equiv.ofInjective g hg).symm ⟨g z, ⟨z, rfl⟩⟩) = h z
  rw [hsymm]

/-! ### Permutation units -/

section Perm

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The permutation unit `Σⱼ s_{τ(π j)} t_{τ j}` of a complete code. -/
def permUnit (τ : AryPrefixCode κ ι) (hτ : F.IsComplete τ) (π : Equiv.Perm κ) : Aˣ where
  val := ∑ j, F.wordS (τ.word (π j)) * F.wordT (τ.word j)
  inv := ∑ j, F.wordS (τ.word j) * F.wordT (τ.word (π j))
  val_inv := by
    rw [Finset.sum_mul]
    calc ∑ j, F.wordS (τ.word (π j)) * F.wordT (τ.word j) *
          ∑ l, F.wordS (τ.word l) * F.wordT (τ.word (π l))
        = ∑ j, F.wordS (τ.word (π j)) * F.wordT (τ.word (π j)) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum, Finset.sum_eq_single j]
          · rw [show F.wordS (τ.word (π j)) * F.wordT (τ.word j) *
                (F.wordS (τ.word j) * F.wordT (τ.word (π j))) =
              F.wordS (τ.word (π j)) * (F.wordT (τ.word j) * F.wordS (τ.word j)) *
                F.wordT (τ.word (π j)) from by noncomm_ring,
              F.wordT_mul_wordS_self, mul_one]
          · intro l _ hl
            rw [show F.wordS (τ.word (π j)) * F.wordT (τ.word j) *
                (F.wordS (τ.word l) * F.wordT (τ.word (π l))) =
              F.wordS (τ.word (π j)) * (F.wordT (τ.word j) * F.wordS (τ.word l)) *
                F.wordT (τ.word (π l)) from by noncomm_ring,
              F.prefixCode_orthogonal τ j l, if_neg (Ne.symm hl), mul_zero, zero_mul]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
      _ = ∑ i, F.cylinder (τ.word i) := Equiv.sum_comp π (fun i ↦ F.cylinder (τ.word i))
      _ = 1 := hτ
  inv_val := by
    rw [Finset.sum_mul]
    calc ∑ j, F.wordS (τ.word j) * F.wordT (τ.word (π j)) *
          ∑ l, F.wordS (τ.word (π l)) * F.wordT (τ.word l)
        = ∑ j, F.wordS (τ.word j) * F.wordT (τ.word j) := by
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [Finset.mul_sum, Finset.sum_eq_single j]
          · rw [show F.wordS (τ.word j) * F.wordT (τ.word (π j)) *
                (F.wordS (τ.word (π j)) * F.wordT (τ.word j)) =
              F.wordS (τ.word j) * (F.wordT (τ.word (π j)) * F.wordS (τ.word (π j))) *
                F.wordT (τ.word j) from by noncomm_ring,
              F.wordT_mul_wordS_self, mul_one]
          · intro l _ hl
            rw [show F.wordS (τ.word j) * F.wordT (τ.word (π j)) *
                (F.wordS (τ.word (π l)) * F.wordT (τ.word l)) =
              F.wordS (τ.word j) * (F.wordT (τ.word (π j)) * F.wordS (τ.word (π l))) *
                F.wordT (τ.word l) from by noncomm_ring,
              F.prefixCode_orthogonal τ (π j) (π l),
              if_neg (π.injective.ne (Ne.symm hl)), mul_zero, zero_mul]
          · intro hj
            exact absurd (Finset.mem_univ j) hj
      _ = 1 := hτ

@[simp] theorem permUnit_val (τ : AryPrefixCode κ ι) (hτ : F.IsComplete τ)
    (π : Equiv.Perm κ) :
    ((F.permUnit τ hτ π : Aˣ) : A) = ∑ j, F.wordS (τ.word (π j)) * F.wordT (τ.word j) :=
  rfl

/-- **Permutation units are scalar moves**, hence central scalars modulo the stably
elementary units. -/
theorem permUnit_mem [Nontrivial A] {k : Type*} [Field k] [Algebra k A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1)
    (τ : AryPrefixCode κ ι) (hτ : F.IsComplete τ) (π : Equiv.Perm κ) :
    F.permUnit τ hτ π ∈ centralClassGroup A := by
  classical
  have hval : ((((F.codeFamily τ hτ).unitsEquiv.symm (F.permUnit τ hτ π)) :
        (Matrix κ κ A)ˣ) : Matrix κ κ A) =
      (F.codeFamily τ hτ).matrixRingEquiv.symm ((F.permUnit τ hτ π : Aˣ) : A) := rfl
  have hU : ((((F.codeFamily τ hτ).unitsEquiv.symm (F.permUnit τ hτ π)) :
        (Matrix κ κ A)ˣ) : Matrix κ κ A) =
      (algebraMap k A).mapMatrix (Matrix.of fun i j ↦ if i = π j then (1 : k) else 0) := by
    rw [hval]
    ext i j
    rw [(F.codeFamily τ hτ).matrixRingEquiv_symm_apply, codeFamily_left, codeFamily_right,
      permUnit_val, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single j]
    · rw [show F.wordT (τ.word i) * (F.wordS (τ.word (π j)) * F.wordT (τ.word j)) *
            F.wordS (τ.word j) =
          (F.wordT (τ.word i) * F.wordS (τ.word (π j))) *
            (F.wordT (τ.word j) * F.wordS (τ.word j)) from by noncomm_ring,
        F.wordT_mul_wordS_self, mul_one, F.prefixCode_orthogonal τ i (π j)]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
      split_ifs <;> simp
    · intro l _ hl
      rw [show F.wordT (τ.word i) * (F.wordS (τ.word (π l)) * F.wordT (τ.word l)) *
            F.wordS (τ.word j) =
          (F.wordT (τ.word i) * F.wordS (τ.word (π l))) *
            (F.wordT (τ.word l) * F.wordS (τ.word j)) from by noncomm_ring,
        F.prefixCode_orthogonal τ l j, if_neg hl, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hmem := (F.codeFamily τ hτ).unitsEquiv_field_matrix_mem_centralClassGroup hdiv
    (algebraMap k A) (fun r x ↦ Algebra.commutes r x)
    (Matrix.of fun i j ↦ if i = π j then (1 : k) else 0)
    ((F.codeFamily τ hτ).unitsEquiv.symm (F.permUnit τ hτ π)) hU
  rwa [MulEquiv.apply_symm_apply] at hmem

/-- A permutation unit acts on the targets of a code-change sum. -/
theorem permUnit_mul_codeChange (τ σ : AryPrefixCode κ ι) (hτ : F.IsComplete τ)
    (π : Equiv.Perm κ) :
    ((F.permUnit τ hτ π : Aˣ) : A) * (∑ j, F.wordS (τ.word j) * F.wordT (σ.word j)) =
      ∑ j, F.wordS (τ.word (π j)) * F.wordT (σ.word j) := by
  rw [permUnit_val, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [show F.wordS (τ.word (π j)) * F.wordT (τ.word j) *
        (F.wordS (τ.word j) * F.wordT (σ.word j)) =
      F.wordS (τ.word (π j)) * (F.wordT (τ.word j) * F.wordS (τ.word j)) *
        F.wordT (σ.word j) from by noncomm_ring,
      F.wordT_mul_wordS_self, mul_one]
  · intro l _ hl
    rw [show F.wordS (τ.word (π j)) * F.wordT (τ.word j) *
        (F.wordS (τ.word l) * F.wordT (σ.word l)) =
      F.wordS (τ.word (π j)) * (F.wordT (τ.word j) * F.wordS (τ.word l)) *
        F.wordT (σ.word l) from by noncomm_ring,
      F.prefixCode_orthogonal τ j l, if_neg (Ne.symm hl), mul_zero, zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

end Perm

/-! ### Merging a sibling group -/

section Merge

variable {κ : Type uκ} [Fintype κ] [DecidableEq κ]

/-- The index type of a merged code: one new word, plus the words outside the image of
the sibling map. -/
abbrev MergeIndex (g : ι → κ) : Type uκ :=
  PUnit.{uκ + 1} ⊕ {j : κ // j ∉ Finset.univ.image g}

/-- The words of a merged code. -/
def mergeWords (word : κ → List ι) (g : ι → κ) (w : List ι) : MergeIndex g → List ι :=
  Sum.elim (fun _ ↦ w) (fun q ↦ word q.1)

omit [DecidableEq ι] [Fintype κ] in
theorem mergeWords_free [Nonempty ι] (σ : AryPrefixCode κ ι) (g : ι → κ) (w : List ι)
    (hg : ∀ z, σ.word (g z) = w ++ [z]) :
    ∀ ⦃p q : MergeIndex g⦄, p ≠ q →
      ¬ mergeWords σ.word g w p <+: mergeWords σ.word g w q := by
  have hout : ∀ (q : {j : κ // j ∉ Finset.univ.image g}) (z : ι), q.1 ≠ g z := by
    intro q z hqz
    exact q.2 (Finset.mem_image.mpr ⟨z, Finset.mem_univ z, hqz.symm⟩)
  obtain ⟨z₀⟩ := (inferInstance : Nonempty ι)
  rintro (_ | q₁) (_ | q₂) hne h
  · exact hne rfl
  · simp only [mergeWords, Sum.elim_inl, Sum.elim_inr] at h
    obtain ⟨e, he⟩ := h
    cases e with
    | nil =>
        rw [List.append_nil] at he
        refine σ.prefix_free (hout q₂ z₀) ?_
        rw [← he, hg z₀]
        exact List.prefix_append w [z₀]
    | cons a e' =>
        refine σ.prefix_free (hout q₂ a).symm ?_
        rw [hg a, ← he]
        exact ⟨e', by rw [List.append_assoc]; rfl⟩
  · simp only [mergeWords, Sum.elim_inl, Sum.elim_inr] at h
    refine σ.prefix_free (hout q₁ z₀) ?_
    rw [hg z₀]
    exact h.trans (List.prefix_append w [z₀])
  · simp only [mergeWords, Sum.elim_inr] at h
    have hne' : q₁.1 ≠ q₂.1 := fun hh ↦ hne (congrArg Sum.inr (Subtype.ext hh))
    exact σ.prefix_free hne' h

/-- The merged code. -/
def mergeCode [Nonempty ι] (σ : AryPrefixCode κ ι) (g : ι → κ) (w : List ι)
    (hg : ∀ z, σ.word (g z) = w ++ [z]) : AryPrefixCode (MergeIndex g) ι :=
  ⟨mergeWords σ.word g w, mergeWords_free σ g w hg⟩

omit [DecidableEq ι] in
/-- Splitting a sum over a code's index type into the sibling group and the rest. -/
theorem sum_merge_split {M : Type*} [AddCommMonoid M] (g : ι → κ)
    (hginj : Function.Injective g) (f : κ → M) :
    ∑ j, f j = ∑ z, f (g z) + ∑ q : {j : κ // j ∉ Finset.univ.image g}, f q.1 := by
  rw [← Finset.sum_add_sum_compl (Finset.univ.image g) f,
    Finset.sum_image fun x _ y _ hxy ↦ hginj hxy]
  refine congrArg₂ (· + ·) rfl ?_
  exact Finset.sum_subtype _ (fun x ↦ Finset.mem_compl) f

theorem mergeCode_isComplete [Nonempty ι] (σ : AryPrefixCode κ ι) (hσ : F.IsComplete σ)
    (g : ι → κ) (hginj : Function.Injective g) (w : List ι)
    (hg : ∀ z, σ.word (g z) = w ++ [z]) :
    F.IsComplete (mergeCode σ g w hg) := by
  have h := hσ
  unfold IsComplete at h ⊢
  rw [sum_merge_split g hginj (fun j ↦ F.cylinder (σ.word j))] at h
  simp only [hg] at h
  rw [← F.cylinder_split w] at h
  rw [Fintype.sum_sum_type, Fintype.sum_unique]
  exact h

/-- The code-change sum of a merged pair of codes. -/
theorem sum_mergeCode [Nonempty ι] (τ σ : AryPrefixCode κ ι) (g : ι → κ)
    (hginj : Function.Injective g) (v w : List ι)
    (hτg : ∀ z, τ.word (g z) = v ++ [z]) (hσg : ∀ z, σ.word (g z) = w ++ [z]) :
    ∑ j, F.wordS (τ.word j) * F.wordT (σ.word j) =
      ∑ p, F.wordS ((mergeCode τ g v hτg).word p) *
        F.wordT ((mergeCode σ g w hσg).word p) := by
  rw [sum_merge_split g hginj (fun j ↦ F.wordS (τ.word j) * F.wordT (σ.word j))]
  simp only [hτg, hσg]
  rw [← F.wordS_mul_wordT_split v w, Fintype.sum_sum_type]
  refine congrArg₂ (· + ·)
    (Fintype.sum_unique fun a₁ : PUnit.{uκ + 1} ↦ F.wordS ((mergeCode τ g v hτg).word (Sum.inl a₁)) *
      F.wordT ((mergeCode σ g w hσg).word (Sum.inl a₁))).symm ?_
  rfl

omit [DecidableEq ι] in
/-- The merged index type is strictly smaller than the code. -/
theorem card_mergeIndex_lt [Nontrivial ι] (g : ι → κ) (hginj : Function.Injective g) :
    Fintype.card (MergeIndex g) < Fintype.card κ := by
  obtain ⟨z₀, z₁, hz⟩ := exists_pair_ne ι
  have hout : ∀ (q : {j : κ // j ∉ Finset.univ.image g}) (z : ι), q.1 ≠ g z := by
    intro q z hqz
    exact q.2 (Finset.mem_image.mpr ⟨z, Finset.mem_univ z, hqz.symm⟩)
  refine Fintype.card_lt_of_injective_not_surjective
    (Sum.elim (fun _ ↦ g z₀) (fun q ↦ q.1) : MergeIndex g → κ) ?_ ?_
  · rintro (_ | q₁) (_ | q₂) he
    · rfl
    · exact absurd he.symm (hout q₂ z₀)
    · exact absurd he (hout q₁ z₀)
    · exact congrArg Sum.inr (Subtype.ext he)
  · intro hsurj
    obtain ⟨p, hp⟩ := hsurj (g z₁)
    rcases p with _ | q
    · exact hz (hginj hp)
    · exact hout q z₁ hp

end Merge

/-! ### The generation theorem -/

/-- **Code-change units are central scalars modulo the stably elementary units**, over any
alphabet with at least two letters. -/
theorem codeChange_mem_centralClassGroup [Nontrivial A] [Nontrivial ι]
    {k : Type*} [Field k] [Algebra k A]
    (hdiv : ∀ x : A, x ≠ 0 → ∃ p q : A, p * x * q = 1) :
    ∀ (n : ℕ) {κ : Type uκ} [Fintype κ] [DecidableEq κ], Fintype.card κ = n →
      ∀ (τ σ : AryPrefixCode κ ι), F.IsComplete τ → F.IsComplete σ →
      ∀ u : Aˣ, (u : A) = ∑ j, F.wordS (τ.word j) * F.wordT (σ.word j) →
      u ∈ centralClassGroup A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro κ _ _ hcard τ σ hτ hσ u hu
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exfalso
      haveI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hcard
      have h := hσ
      unfold IsComplete at h
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact zero_ne_one h
    · obtain ⟨j₀, hj₀⟩ := Fintype.card_eq_one_iff.mp hcard
      have hsum : ∀ (f : κ → A), ∑ j, f j = f j₀ := fun f ↦
        Finset.sum_eq_single j₀ (fun j _ hj ↦ absurd (hj₀ j) hj)
          (fun h ↦ absurd (Finset.mem_univ j₀) h)
      have hs : σ.word j₀ = [] := by
        refine F.eq_nil_of_cylinder_eq_one ?_
        have h := hσ
        unfold IsComplete at h
        rwa [hsum] at h
      have ht : τ.word j₀ = [] := by
        refine F.eq_nil_of_cylinder_eq_one ?_
        have h := hτ
        unfold IsComplete at h
        rwa [hsum] at h
      have hone : u = 1 := Units.ext (by
        rw [hu, hsum, hs, ht, wordS_nil, wordT_nil, one_mul, Units.val_one])
      rw [hone]
      exact one_mem _
  · obtain ⟨w, g, hg⟩ := F.exists_sibling_group σ hσ (by omega)
    obtain ⟨v, h, hh⟩ := F.exists_sibling_group τ hτ (by omega)
    have hinj : ∀ (word : κ → List ι) (base : List ι) (f : ι → κ),
        (∀ z, word (f z) = base ++ [z]) → Function.Injective f := by
      intro word base f hf z₁ z₂ hz
      have h1 : base ++ [z₁] = base ++ [z₂] := by rw [← hf z₁, ← hf z₂, hz]
      exact List.singleton_inj.mp (List.append_cancel_left h1)
    have hginj : Function.Injective g := hinj σ.word w g hg
    have hhinj : Function.Injective h := hinj τ.word v h hh
    obtain ⟨π, hπ⟩ := exists_perm_extending g h hginj hhinj
    have hPmem : F.permUnit τ hτ π ∈ centralClassGroup A :=
      F.permUnit_mem (k := k) hdiv τ hτ π
    have hτ'g : ∀ z, (τ.reindex π).word (g z) = v ++ [z] := by
      intro z
      rw [AryPrefixCode.reindex_word, hπ, hh]
    have hu'val : ((F.permUnit τ hτ π * u : Aˣ) : A) =
        ∑ j, F.wordS ((mergeCode (τ.reindex π) g v hτ'g).word j) *
          F.wordT ((mergeCode σ g w hg).word j) := by
      rw [Units.val_mul, hu, F.permUnit_mul_codeChange τ σ hτ π]
      exact F.sum_mergeCode (τ.reindex π) σ g hginj v w hτ'g hg
    have hlt : Fintype.card (MergeIndex g) < n := by
      rw [← hcard]
      exact card_mergeIndex_lt g hginj
    have hu'mem := ihn _ hlt rfl (mergeCode (τ.reindex π) g v hτ'g) (mergeCode σ g w hg)
      (F.mergeCode_isComplete (τ.reindex π) (F.reindex_isComplete τ hτ π) g hginj v hτ'g)
      (F.mergeCode_isComplete σ hσ g hginj w hg) _ hu'val
    have hassemble : u = (F.permUnit τ hτ π)⁻¹ * (F.permUnit τ hτ π * u) := by group
    rw [hassemble]
    exact mul_mem (inv_mem hPmem) hu'mem

end CompleteMatrixFamily
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.eq_nil_of_cylinder_eq_one
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_sibling_group
#audit_axioms GroupApproximation.CompleteMatrixFamily.exists_perm_extending
#audit_axioms GroupApproximation.CompleteMatrixFamily.permUnit_mem
#audit_axioms GroupApproximation.CompleteMatrixFamily.mergeCode_isComplete
#audit_axioms GroupApproximation.CompleteMatrixFamily.sum_mergeCode
#audit_axioms GroupApproximation.CompleteMatrixFamily.card_mergeIndex_lt
#audit_axioms GroupApproximation.CompleteMatrixFamily.codeChange_mem_centralClassGroup
